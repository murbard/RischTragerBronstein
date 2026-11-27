# RischTragerBronstein

A Lean 4 / Mathlib formalisation of symbolic integration in finite terms (Liouville, Risch, Trager,
Bronstein), built so that **both answers are theorems**:

* if an integrator answers *yes*, the integrand has an elementary integral
  (`Differential.HasElementaryIntegral`, Bronstein Def. 5.1.3 — constants may grow);
* if it answers *no*, **no** elementary extension contains an antiderivative.

No `sorry`, no extra axioms, no `native_decide` (every headline theorem depends only on `propext`,
`Classical.choice`, `Quot.sound`). Kernel computations use `decide +kernel`.

## Status — what is decided, with verified executables

| Field | Procedure | Theorem |
|---|---|---|
| `R(x)` | `CPoly.integrateRational` | `integrateRational_correct`, `ratFunc_hasElementaryIntegral` |
| `R(x)(t)`, `t′ = η ∈ R(x)` any primitive (`log x`, `log b(x)`, `arctan x`, …) | `Tower.integratePrim` | `Tower.integratePrim_decides` (iff) |
| `R(x)(t)`, `t = exp a(x)`, `a ∈ R[x]` | `Tower.integrateExp` | `Tower.integrateExp_decides` (iff) |
| `R(x)(t)`, `t′ = η t`, `η ∈ R(x)` without simple poles (`t = exp a(x)`, `a ∈ R(x)`) | `Tower.integrateHyperexp` | `Tower.integrateHyperexp_decides` (iff) |
| `R(x)(t)`, `t′ = η t`, **`η ∈ R(x)` arbitrary** (simple poles allowed: `exp (arctan x)`, `η = 1/(x²+1)`, …; `t` certified to be a monomial by `CPoly.hyperexpMonomialCheck`; constants with `HasRatRoots`/`HasNatTest`, e.g. `ℚ`) | `Tower.integrateHyperexpW` | `Tower.integrateHyperexpW_decides` (iff) |
| `R(x)(t₁)(t₂)`, two independent primitives over `R(x)` (`log x`, `log (x + 1)`, …) | `Tower.integratePrim2` | `Tower.integratePrim2_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, nested logarithm `t₂ = log u`, `u ∈ R(x)(t₁) ∖ R(x)` (`log log x`, `log (x + log x)`, …) | `Tower.integrateNestedLog` | `Tower.integrateNestedLog_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, non-elementary nested primitive `t₂′ = W ∈ R(x)(t₁)`, the residues of `W` not constant (`li x = ∫ dx / log x`, …) | `Tower.integrateLi` | `Tower.integrateLi_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **mixed tower**: `t₁` a primitive, `t₂ = exp a(x)`, `a ∈ R[x]` (`ℚ(x, log x, eˣ)`, …) | `Tower.integrateExpPrim` | `Tower.integrateExpPrim_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **two exponentials** `t₁ = exp a₁`, `t₂ = exp a`, `a₁, a ∈ R[x]` independent (`ℚ(x, e^{x²}, eˣ)`, …) | `Tower.integrateExpExp` | `Tower.integrateExpExp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **logarithm over an exponential** `t₁ = exp a₁`, `t₂ = log U`, `U ∈ R(x)(t₁)` (`ℚ(x, eˣ, log (eˣ + 1))`, …) | `Tower.integratePrimExp` | `Tower.integratePrimExp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **non-elementary primitive over an exponential** `t₁ = exp a₁`, `t₂′ = W ∈ R(x)(t₁)` with non-constant residues (`t₂ = ∫ dx / (eˣ + x)`, …) | `Tower.integrateLiExp` | `Tower.integrateLiExp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, `t₁` primitive, **`t₂′ = η t₂` with `η ∈ R(x)` arbitrary** (certified monomial; `ℚ(x, log x, exp (arctan x))`, …) | `Tower.integrateHexpPrim` | `Tower.integrateHexpPrim_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **logarithm over a general hyperexponential** `t₁′ = η t₁`, `η ∈ R(x)` arbitrary (certified monomial), `t₂ = log U`, `U ∈ R(x)(t₁)` (`ℚ(x, exp (arctan x), log (exp (arctan x) + x))`, …) | `Tower.integratePrimHexp` | `Tower.integratePrimHexp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **non-elementary primitive over a general hyperexponential** `t₁′ = η t₁`, `η ∈ R(x)` arbitrary (certified monomial), `t₂′ = W ∈ R(x)(t₁)` with non-constant residues (`t₂ = ∫ dx / (exp (arctan x) + x)`, …) | `Tower.integrateLiHexp` | `Tower.integrateLiHexp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **exponential over a general hyperexponential** `t₁′ = η t₁`, `η ∈ R(x)` arbitrary (certified monomial), `t₂ = exp a(x)`, `a ∈ R[x]`, independent (certified by `CPoly.hexpExpIndep`; `ℚ(x, exp (arctan x), eˣ)`, …) | `Tower.integrateExpHexp` | `Tower.integrateExpHexp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **two general hyperexponentials** `t₁′ = η₁ t₁`, `t₂′ = η₂ t₂`, `ηᵢ ∈ R(x)` arbitrary (certified monomials), independent (certified by `CPoly.hexpHexpIndep`; `ℚ(x, exp (arctan x), exp (1/x))`, …) | `Tower.integrateHexpHexp` | `Tower.integrateHexpHexp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, **exponential with argument in a general hyperexponential tower** `t₁′ = η t₁`, `η ∈ R(x)` arbitrary (certified monomial), `t₂ = exp a`, `a ∈ R(x)[t₁]`, `a′` of positive `t₁`-degree (`exp (exp (arctan x))`, …) | `Tower.integrateExpArgHexp` | `Tower.integrateExpArgHexp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `Kc(x)(t₀)(t₁)…(t_{n-1})` (`Kc ⊇` all constants), **any number `n` of primitives** `tₘ′ = ηₘ ∈ ℚ(x)` (`log x, log (x + 1), …, arctan x, …`), independent (certified by `Tower.PrimN.primCert`, which is itself decided by the algorithm at lower heights) | `Tower.PrimN.elemP` (with parametric limited integration `limIntP` at every level) | `Tower.PrimN.PrimTower.primN_decides` (iff, **every height**; examples at heights 2, 3, 4 in `Computable/PrimNExample.lean`) |
| `Kc(x)(t₀)…(t_{n-1})`, **mixed towers of any height**: each `tₘ` a primitive `tₘ′ = ηₘ ∈ ℚ(x)` or an exponential or hyperexponential `tₘ′ = bₘ tₘ`, `bₘ ∈ ℚ(x)` (`exp ∫ bₘ`, e.g. `exp(1/x)`, `exp(arctan x)`), in any order (`ℚ(x, log x, eˣ)`, `ℚ(x, eˣ, exp(x²))`, `ℚ(x, log x, log (x+1), eˣ)`, `ℚ(x, log x, exp(1/x))`, `ℚ(x, log x, eˣ, exp(arctan x))`, …); certificate `Tower.MixN.mixCert` (primitives not derivatives; exponents `ℚ`-independent, and no `ℚ`-combination of them a logarithmic derivative: `logIndepCert`) | `Tower.MixN.elemM` (with the Risch equation `rdeM` and limited integration `limIntM` at every level) | `Tower.MixN.MixTower.mixN_decides` (iff, **every height**; examples `∫ exp(x²)`, `∫ eˣ log x`, `∫ eˣ exp(x²)`, `∫ exp(1/x)`, `∫ exp(1/x) log x`, `∫ exp(arctan x) log x` not elementary, in `Computable/MixNExample.lean`) |
| `Kc(x)(t₀)…(t_{n-1})`, **primitives with nested data, any height**: `tₘ′ = ηₘ ∈ Kc(x, t₀, …, t_{m-1})` (`log x`, `log log x`, `li`-type primitives `∫ dx/log x`, …); certificate `Tower.NestP.nestCert` (no `ηₘ` a derivative in `F m`, decided by parametric limited integration) | `Tower.NestP.elemN` (parametric elementary integration `paramElem`, with parametric limited integration `paramLim` at every level) | `Tower.NestP.NestTower.nestN_decides` (iff, **every height**; examples `∫ dx/log x`, `∫ log log x dx` not elementary, `∫ (log log x + 1/log x) dx` elementary, in `Computable/NestPExample.lean`) |
| `Kc(x)(t₀)…(t_{n-1})`, **exponentials with nested arguments, any height**: `tₘ = exp aₘ`, `aₘ ∈ Kc(x, t₀, …, t_{m-1})` (`eˣ`, `exp(eˣ)`, `e^{x²}`, `exp(x eˣ)`, …); certificate `Tower.NestM.expCertM` (each `aₘ′` is not a `ℚ`-combination of the previous exponents' derivatives, decided by a constant system) | `Tower.NestM.elemNM` (parametric elementary integration `paramElemM`, with parametric limited integration `paramLimM` and the **parametric Risch differential equation** `prde` at every level) | `Tower.NestM.NestMTower.nestM_decides` (iff, **every height**; examples `∫ exp(eˣ) dx`, `∫ e^{x²} dx` not elementary, `∫ eˣ exp(eˣ) dx`, `∫ x e^{x²} dx` elementary, in `Computable/NestMExample.lean`) |
| `Kc(x)(t₀)…(t_{n-1})`, **mixed towers of logarithms and exponentials with nested data, any height**: each `tₘ = log vₘ` (`tₘ′ = ηₘ = vₘ′/vₘ`) or `tₘ = exp aₘ`, with `vₘ, aₘ ∈ Kc(x, t₀, …, t_{m-1})`, in any order (`xˣ = exp(x log x)`, `√x eˣ = exp(x + ½ log x)`, `log(eˣ+1)`, `exp(log² x)`, …); certificate `Tower.NestX.certX` (each `ηₘ = vₘ′/vₘ` has no antiderivative in `F m`, decided by `paramLimX`; each `aₘ′` is not a `ℚ`-combination of the previous generators' derivatives, decided by a constant system) | `Tower.NestX.elemNX` (parametric elementary integration `paramElemX`, parametric limited integration `paramLimX`, and the **parametric Risch equation `prdeX` for `f = h′ + ∑ cⱼ wⱼ′/wⱼ`** at every level) | `Tower.NestM.NestMTower.nestX_decides` (iff, **every height**; examples `∫ xˣ dx`, `∫ √x eˣ dx`, `∫ log(eˣ+1) dx` not elementary, `∫ (1 + log x) xˣ dx` elementary, in `Computable/NestXExample.lean`) |
| `R(x)(t₁)(t₂)`, `t₁` primitive, **`t₂ = exp a` with `a ∈ R(x)[t₁]`**, `deg_{t₁} a′ ≥ 1` (`x^x = exp (x log x)`, `exp (log² x)`, …) | `Tower.integrateExpArgPrim` | `Tower.integrateExpArgPrim_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `R(x)(t₁)(t₂)`, `t₁ = exp a₁`, **`t₂ = exp a` with `a ∈ R(x)[t₁]`**, `a′` of positive `t₁`-degree (`e^{eˣ}`, `exp (x eˣ)`, `exp (eˣ + 2x)`, …; constants with `HasNatTest`, e.g. `ℚ`) | `Tower.integrateExpArgExp` | `Tower.integrateExpArgExp_decides`, `_decides_val`, `_decides_concrete` (iff) |
| `Kc(x, y)`, `y² = q(x)`, **`q ∈ ℚ[x]` squarefree of any degree ≥ 1** (genus 0, elliptic, hyperelliptic of any genus, odd or even degree, no rational point needed), integrand **`A/D + (B/C) y`** arbitrary | `Jac.hypDecideAll` (Hermite reduction, splitting fields `splitFieldG`/`towerEven`, torsion by reduction at two good primes, logarithmic certificates) | `Jac.hypDecideAll_decides` (iff; the procedure answers for every large search bound `N`) |
| `Kc(x, y)`, **superelliptic `yⁿ = p(x)`**, `p ∈ F[x]` squarefree, `gcd(n, deg p) = 1` (`F` any computable char-0 field ⊆ constants), integrand **`B(x) yʲ / p(x)ᵏ`**, `0 < j < n`, `k ≥ 1`, i.e. **`∫ B(x) p(x)^{a/n} dx` for every exponent `a/n ∉ ℤ`** (residue-free class; `∫ dx/∛(x²+1)`, `∫ ∛(x²+1) dx`, `∫ dx/(x²+1)^{4/3}` not elementary, `∫ x dx/∛(x²+1)`, `∫ x dx/(x²+1)^{4/3}` elementary) | `CPoly.supHerm` (Hermite steps on the power of `p`) then `CPoly.supRed` (reduction `B = C′p + (j/n) C p′ + B₀`, `deg B₀ ≤ deg p − 2`) | `Differential.super_decides_pow` / `super_decides` (iff; examples in `Algebraic/SuperExample.lean`) |
| `Kc(x, y)`, **arbitrary curve `F(x, y) = 0` over `ℚ`** (`F` monic in `y`, irreducible over `Kc(x)`), integrand `A(x, y)/D(x)` with `shapeOK` (a decidable shape condition on the input lists) | `decideTotal Fc A D N` (automatic pipeline `decideCurveQ`, then exhaustive enumeration of certificates: number field, branch data, Möbius transformation, logarithmic and non-torsion witnesses) | `decideTotal_decides` (`Torsion/CertExistsFinal.lean`): for every large `N` it answers, and the answer is the iff; the enumeration is a proof of decidability, not a practical search |
| `Kc(x, y)(t)`, **one exponential `t = exp a` over an arbitrary curve** (`a ∈ Kc(x, y)`, curve over `ℚ`, integrand `A(t)/D(t)` with coefficients in the function field; e.g. `∫ eˣ/√(x³+1)`) | `integrateExpCurve Fc a A D N` (Hermite in `t`, residue test, Risch equations on the curve by `curveRde`, constant term by `decideTotal`) | `integrateExpCurve_decides` (`Mixed/ExpCurveMain.lean`): for every large `N` it answers, and the answer is the iff |
| `Kc(x, y)(t)`, **one logarithm `t = log u` over an arbitrary curve** (`u ∈ Kc(x, y)`, curve over `ℚ`; e.g. `∫ log x/√(x³+1)`, `∫ 1/(x log x)`) | `integrateLogCurve Fc u A D N` (Hermite in `t`, residue test, polynomial part by the limited-integration chain `primChain` on the curve, constant term by `decideTotal`) | `integrateLogCurve_decides` (`Mixed/LogCurveMain.lean`): for every large `N` it answers, and the answer is the iff |
| `Kc(x, y)(t₀)…(t_{k-1})`, **towers of logarithms of any height over an arbitrary curve** (`tₘ = log uₘ`, `uₘ` in the previous level: `log x`, `log log x`, `log(y + log x)`, …; curve over `ℚ`) | `Curves.LT.elT Fc us k q N` (at each level: Hermite in `tₘ`, residue test, the limited-integration chain `lchain` with the parametric exact solver `lex` one level down, constant term one level down; at the base `decideTotal`) | `Curves.LT.elT_decides` (`Mixed/LTMain.lean`): for every realization of height `k` with algebraically closed constants, for every large `N` it answers, and the answer is the iff (plus an integral over every elementary extension) |
| `Kc(x, y)(t₀)…(t_{k-1})`, **mixed towers of logarithms and exponentials of any height over an arbitrary curve** (`tₘ′ = ηₘ` with `ηₘ = vₘ′/vₘ`, or `tₘ = exp aₘ`; `ηₘ, vₘ, aₘ` in the previous level; curve over `ℚ`; e.g. `eˣ`, `log(eˣ + 1)`, `exp(log x · y)`) | `Curves.MT.elM Fc ks lv k q N` (log level: Hermite, residue test, chain `mchain` with parametric limited integration `paramLimC` one level down, constant term one level down; exp level: split `tⁿ`, Hermite, residue test, Risch equations by the parametric solver `prdeC` one level down, constant term one level down; base `decideTotal`) | `Curves.MT.elM_decides_any` (`Mixed/MTFinal.lean`): for every realization of height `k` generating `L`, whose certificate `certC` holds (computable; it proves transcendence and no new constants), **over any constant field of characteristic zero**, for every large `N` it answers, and the answer is the iff (plus an integral over every elementary extension); **every answer at any bound is correct** (`elM_sound`, `Mixed/MTSound.lean`: answers persist for larger bounds, `elM_mono`, since the base search is a prefix search). Height `0` is the curve itself: `decideTotal` over any constants |
| **Elementary expressions** over an arbitrary curve (`x`, `y`, rationals, `+`, `·`, `−`, `⁻¹`, `exp`, `log`, nested; e.g. `exp(x²)`, `1/log x`, `log log x`, `exp(eˣ) eˣ`, `log x/y` on a conic) | `Curves.MT.Front.frontDecide Fc e N` (`Mixed/FrontExpr.lean`): the `exp`/`log` subexpressions become the levels of a tower (`nodesOf`, kinds `ksOf` built level by level), the expression is compiled to a code (`comp`), the tower is certified (`certC`), then `elM` | `Curves.MT.Front.front_decided`: for every realization of the compiled tower generated by it, for every large `N` it answers, and the answer is the iff (the code has the value of the expression, `comp_spec`; the generators are exponentials/logarithms of the subexpressions, `front_nodes`). Dependent generators (`exp x` with `exp 2x`) fail `certC`: `none`; `frontDecideN` first normalizes (`exp(a + b) = exp a exp b`, `exp(n a) = (exp a)ⁿ`, `exp(log a) = a`, `log(a b) = log a + log b`, `log(exp a) = a`), so `∫ eˣ e^{2x}`, `∫ e^{x + log x}`, `∫ log(x²)/x` are decided (the guarantee is for the normalized expression). `frontDecideN2` also picks common generators for rational multiples (`exp(c u) = exp(u/D)^{cD}`), so `∫ e^{x/2} eˣ` is decided; only relations with non-zero additive constants (`exp(x + 1)` with `exp x`) remain `none`. Every answer is correct at any bound (`front_sound`). Kernel-checked theorems in `Mixed/FrontExprExamples.lean` for every realization over any constants: **`∫ dx/log x`, `∫ exp(x²)`, `∫ log log x` not elementary, `∫ x exp(x²)` elementary**. With a radical of a rational function (`Mixed/FrontRadical.lean`, `frontDecideR`, `frontDecideR_sound`): `root n a`, `a = p/q`, gives the base curve `yⁿ = p qⁿ⁻¹` with `y/q` an `n`-th root of `a` (`root_value`); e.g. `∫ x/√(x² + 1)` is answered `true` (`#eval`, about 2.5 min). **With a square root over the top level** (`Mixed/FrontSqrt.lean`, `frontSqrt a e₁`): `∫ e₁ √a` for expressions `a`, `e₁`, when `a` compiles to a squarefree polynomial `A(t)` of odd degree in the top generator and the denominator of `e₁` is `c tᵏ Aˡ` (found by exact divisions, `stripG`), dispatched to `keDecide` below an exponential and to `kpDecideK` below a logarithm; `frontSqrt_sound`: every answer is correct for every realization and every square root `θ` of `a` generating `L`. Examples (`Mixed/FrontSqrtExamples`, `#guard`, seconds): `∫ √(eˣ + 1)`, `∫ eˣ√(eˣ + 1)`, `∫ 1/√(eˣ + 1)`, `∫ √(log x)/x`, `∫ (1 + 1/x)/√(x + log x)` elementary; `∫ √(eˣ + x)`, `∫ √(log x)`, `∫ √(x + log x)` not elementary. With the antiderivative (`Mixed/FrontSqrtW.lean`): `frontSqrtEW` mirrors `frontSqrtE` (`frontSqrtEW_isSome`) and returns the witness of `keDecideCW` below an exponential or `y` from `kpSolveK` below a logarithm (`kpK_antiderivative`: `(y θ)′ = B/Aᵏ θ`), valid for every realization (`frontSqrtEW_valid`, `SqW.Valid`); `frontSqrtShow` prints it (`Mixed/FrontSqrtWExamples`, `#guard`: `∫ √(eˣ + 1) = 2√(eˣ + 1) + 2 log(1 − √(eˣ + 1)) − log(−eˣ)`, `∫ eˣ√(eˣ + 1) = (2/3)(1 + eˣ)√(eˣ + 1)`, `∫ √(log x)/x = (2/3) log x √(log x)`, `∫ (1 + 1/x)/√(x + log x) = 2√(x + log x)`). **With poles** (`Mixed/FrontSqrtPole.lean`, `frontSqrtP a e₁ cs`): the poles `c_q` given as expressions one level below the top, the denominator of `e₁` checked to be `c tᵏ ∏(t − c_q) Aˡ` by exact divisions (`divLins`), dispatched to `kqDecide` (logarithm) or `kxDecide` (exponential); `frontSqrtP_sound` (`ev_pair_scale`). Examples (`Mixed/FrontSqrtPoleExamples`): `∫ √(log x)/(x(log x − 1))`, `∫ √(eˣ + 1)/(eˣ − 1)` elementary, `∫ √(log x)/(log x − 1)` not. **With an `n`-th root over a logarithm** (`Mixed/FrontRoot.lean`, `frontRootLog n a [e₀, e₁, …]`): `∫ ∑ⱼ eⱼ θʲ`, `θⁿ = a`, with `a` a squarefree polynomial in the top logarithm, `gcd(n, deg a) = 1`, denominators `c aᵏ` for `j ≥ 1`: `e₀` by `elM`, the others by `kpDecideK` (the components decouple, `kl_iff`); `frontRootLog_sound`. Examples (`Mixed/FrontRootExamples`): `∫ (log x)^{1/3}/x`, `∫ (1 + (log x)^{2/3})/x` elementary, `∫ (log x)^{1/3}` not. **Whole integrands `e₀ + e₁ √a`** over a top level of either kind (`Mixed/FrontSqrtSum.lean`, `frontSqrtSum`): `e₀` by `elM`, `e₁ √a` by `frontSqrtE`, elementary iff both are (`kl_componentsW`; conversely `add_in` with `e₀` integrable over every elementary extension, lifted by `isElementary_alg`); `frontSqrtSum_sound`. Examples (`Mixed/FrontSqrtSumExamples`): `∫ (eˣ + √(eˣ + 1))`, `∫ (1 + √(log x))/x` elementary; `∫ (eˣ/x + √(eˣ + 1))`, `∫ (1/log x + √(log x)/x)` not. With the antiderivatives: `frontSqrtSumW` (`elMW` pieces for `e₀`, the square-root witness for `e₁ √a`; `frontSqrtSumW_isSome`, `frontSqrtSumW_valid`, printed by `frontSqrtSumShow`, `Mixed/FrontSqrtSumWExamples`), and `frontSqrtPW` with poles (the witnesses of `kqDecideCW`/`kxDecideCW`; `frontSqrtPW_isSome`, `frontSqrtPW_valid`, `Mixed/FrontSqrtPoleW`). **Arbitrary rational expressions in `√a`** (`Mixed/FrontSqrtAuto.lean`, `frontSqrtAuto a s`): `s : SE` has `√a` as an atom (`exp`/`log` of `√a`-free arguments); `SE.split` rewrites it as `e₀ + e₁ √a` by arithmetic in the quadratic extension (`(u₀ + u₁θ)⁻¹ = (u₀ − u₁θ)/(u₀² − u₁²a)`), then `frontSqrtSum`; `SE.split_spec` (correct when `θ` is not in a field containing the values, also at `0⁻¹ = 0`), `theta_notMem` (`X² − A` is the minimal polynomial over `Fₘ₊₁`), `frontSqrtAuto_sound`, and `frontSqrtAutoW_valid` with the antiderivative. Examples (`Mixed/FrontSqrtAutoExamples`): `∫ 1/√(eˣ + 1)`, `∫ eˣ/(√(eˣ + 1) + 1)`, `∫ (1 + √(log x))²/x` elementary, `∫ (log x)^{3/2}` not. **Arbitrary rational expressions in an `n`-th root over a logarithm** (`Mixed/FrontRootAuto.lean`, `frontRootAuto n a s`): `SE.splitN` rewrites `s` as `∑_{j<n} eⱼ θʲ`, products by the multiplication matrix (`mul_lemma`), inverses by the first column of the adjugate over the determinant (symbolic determinants `detE`; `inv_lemma` in `Mixed/RootArith.lean`, valid also for the element `0`), then `frontRootLog`; `SE.splitN_spec` (needs `1, θ, …, θⁿ⁻¹` independent over a field containing the values: `theta_indep`, `Xⁿ − A` is the minimal polynomial over `Fₘ₊₁`), `frontRootAuto_sound`, `frontRootAutoW_valid`. Examples (`Mixed/FrontRootAutoExamples`): `∫ 1/(x (log x)^{1/3}) = (3/2)(log x)^{2/3}`, `∫ (1 + (log x)^{1/3})²/x`, `∫ (θ + 1)/(xθ)` elementary, `∫ (log x)^{-1/3}`, `∫ (log x)^{2/3}` not. Inverses whose norm is not a power of `a` (e.g. `1/(1 + θ)`) give denominators outside `frontRootLog`'s shape: answer `none` (such integrands, with the poles and a number field for the residues given, are decided by `kvDecide`, see below, reached from expressions by `frontRootAutoP`). **`n`-th roots with poles, from expressions** (`Mixed/FrontRootPole.lean`, `FrontRootSumP.lean`, `FrontRootAutoP.lean`): `frontRootP M n j zN gs a e₁ cs` decides `∫ e₁ θʲ`, `θⁿ = a` over a logarithm, the denominator of `e₁` checked to be `c ∏(t − c_q) Aˡ` by exact divisions and dispatched to `kvDecide` with the number field `ℚ[X]/(M)` (`frontRootP_sound`); `frontRootSumP` decides whole integrands `∑_{j<n} eⱼ θʲ` (`e₀` by `elM`, pole-free components by `kpDecideK`, components with poles by `kvDecide`; `frontRootSumP_sound`: the components decouple by `kl_componentsW`, and conversely positive answers hold over every elementary extension — `kvDecide_in`, `Mixed/KVIn.lean` — so they add up); `frontRootAutoP` splits an arbitrary rational expression in `θ` by `SE.splitN` first (`frontRootAutoP_sound`). Examples (`Mixed/FrontRootPoleExamples`, `FrontRootSumPExamples`, `FrontRootAutoPExamples`, `#guard`, 2–4 min each file): `∫ ∛(log x)/(x(log x − 1))`, `∫ (1/x + θ/(x(log x − 1)) + θ²/x)`, **`∫ dx/(x(1 + ∛(log x)))`** elementary; `∫ ∛(log x)/(log x − 1)`, `∫ dx/(1 + ∛(log x))` not. **With poles** (`Mixed/FrontSqrtSumP.lean`): `frontSqrtPE` is `frontSqrtP` over a given tower expression; `frontSqrtSumP a e₀ e₁ cs` (`e₀` by `elM`, `e₁ √a` with poles `cs` by `frontSqrtPE`; `frontSqrtSumP_sound`, `frontSqrtSumPW_valid`) and `frontSqrtAutoP a s cs` (`s` rational in `√a`, split by `SE.split`; `frontSqrtAutoP_sound`, `frontSqrtAutoPW_valid`). Examples (`Mixed/FrontSqrtSumPExamples`): `∫ 1/(x(1 + √(log x)))` elementary, `∫ 1/(1 + √(log x))` not (seconds). **Non-Kummer algebraic functions over a logarithm** (`Mixed/FrontNK.lean`, `frontNKLog ps es`): `∫ ∑ⱼ eⱼ θʲ` for `θⁿ + ∑ aᵢ θⁱ = 0`, the coefficients compiling to polynomials in the top logarithm and the curve with a single place at infinity (`nkShape`): power sums `traceCodes` (checked by `traceC`), the candidate from the shape (`nkCandV`) in `searchTVP`, the trace part by `elM`; `frontNKLog_sound` (via `nk_iffTV`). Examples (`Mixed/FrontNKExamples`, about 30 s each): for `θ³ + θ = x log x`, `∫ θ` and `∫ θ²` are not elementary. **Antiderivatives from every front end**: `frontRootLogW` (`elMW` pieces for `e₀`, `yⱼ` with `(yⱼ θʲ)′ = eⱼ θʲ` from `kpSolveK`; `frontRootLogW_isSome`, `frontRootLogW_valid`, `frontRootLogShow`, `Mixed/FrontRootW`), `frontNKLogW` (the trace part by `elMW`, the exact part `∑ Yₖ θᵏ` by `exactTLSW` on the shape candidate; `frontNKLogW_isSome`, `frontNKLogW_valid`: `∑ eⱼ θʲ = τ + (∑ Yₖ θᵏ)′`, `frontNKLogShow`, `Mixed/FrontNKW`), besides `frontSqrtEW`, `frontSqrtSumW`, `frontSqrtPW` above |
| **Rational expressions in an `n`-th root over the top level** (`θⁿ = a`, `a` an expression compiling to a squarefree polynomial `A(t)` of degree prime to `n` in the top generator `t`, a logarithm **or an exponential**; e.g. `∛(x + eˣ)`, `∛(1 + eˣ)/(eˣ − x)`, `1/(1 + ∛(log x))`) | `Curves.MT.Front.frontRootAutoX M n zN a s pls gss` (`Mixed/FrontRootAutoX.lean`): the expression `s : SE` rational in `θ` is split as `∑_{j<n} eⱼ θʲ` (`SE.splitN`, adjugate inverses in `K(θ)`), and `frontRootSumX` (`Mixed/FrontRootSumX.lean`) decides the components: `e₀` by `elM`; below a logarithm `rootComp` (`kpDecideK` without poles, `kvDecide` with the poles `pls[j]`); below an exponential `rootCompE` (denominator `c tᵏ ∏(t − c_q) Aˡ` by exact divisions; `krDecide` without poles, `kyDecide` with poles and the roots `gss[j]` of the residue invariants in the number field `ℚ[X]/(M)`). Logarithmic top levels alone: `frontRootSumP`, `frontRootAutoP` (`Mixed/FrontRootSumP.lean`, `FrontRootAutoP.lean`) | `frontRootAutoX_sound`, `frontRootSumX_sound`: every answer is correct for every realization of the compiled tower and every `n`-th root `θ` of `a` generating `L`. The components decouple (`kl_componentsW`) and, conversely, integrable components add up by **`HasElementaryIntegral.sum`** (`Elementary/CommonExt.lean`: elementary integrals persist over every differential extension field and therefore add — no common-extension hypothesis). Examples (`Mixed/FrontRootXExamples`, `FrontRootAutoPExamples`, `#guard`): `∫ ∛(x + eˣ)` and `∫ ∛(1 + eˣ)/(eˣ − x)` not elementary, `∫ (eˣ + ∛(1 + eˣ))` elementary; `∫ 1/(1 + ∛(log x))` not elementary, `∫ 1/(x(1 + ∛(log x)))` elementary |
| **Square root of a cubic over an exponential level, with poles: the Mordell–Weil case** (`θ² = A(t)`, `deg A = 3`, `t = exp`, linear base, any level; e.g. `∫ √(e³ˣ − eˣ + x²)/(x(eˣ − 1))`) | `Curves.MT.MTower.kxDecideNC` / `kxSearch` / `kxAuto` (`Mixed/KXAllLevels.lean`, `KXSearch.lean`, `KXAuto.lean`), from expressions `Curves.MT.Front.frontSqrtPAuto` (`Mixed/FrontSqrtPoleNC.lean`): relation search for dependent classes, otherwise independence certificates in the Mordell–Weil group of the elliptic curve over `Kₘ(X)` — Manin-map certificates (fast path), canonical-height certificates, descent for curves constant up to scaling (`stepI`, `recKF`) | **`kxDecideNC_decides`**, **`kxAuto_decides`**, **`frontSqrtPAuto_decides`**: eventual, persistent, correct answers — **unconditionally** (standard axioms). Completeness of the height certificate is **`ExH.certQ_exists_nc`** (`Mixed/ExH*.lean`): on every `y² = x³ + A x + B` over `K(X)` not constant up to scaling, `k · ĥ` is natural-valued for some `k > 0` and `ĥ` vanishes only on torsion (`ExH.hint_htor`), proved elementarily (points of everywhere non-singular reduction form a subgroup of finite exponent on which the weighted height quadruples exactly under doubling); no Manin kernel theorem, no Lang–Néron theorem |
| **Antiderivatives**, not only answers: elementary expressions and mixed towers over a curve | `Curves.MT.elMW` (`Mixed/MTWit.lean`) mirrors `elM` and returns, when the integral is elementary, the pieces of an antiderivative per level `tₘ`: the Hermite part `gn/gd`, the polynomial part (the limited-integration chain `mchainW` below a logarithm, the Risch-equation solutions `rdeSolM` below an exponential, `pc/t^kk`) and the logarithmic part `∑_{s(α)=0} r(α) log (t − α)` (`log (1 − α/t)` below an exponential; `r` the residue polynomial); at the base, the remaining integrand on the curve. `Curves.MT.Front.frontIntegrate` / `integrateShow` (`Mixed/FrontIntegrate.lean`) print it | `elMW_isSome` (answers exactly as `elM`), `MTower.elMW_valid` (`Mixed/MTWitSound.lean`: every returned witness is valid — `q = (gn/gd + pc/t^kk)′ + b/s + c₀` level by level, `s` separable, residue test passed, the base integrand has an elementary integral), `LevelOK.rootSum` (`b/s = ∑ r(α) (t − α)′/(t − α) − (∑ r(α)) e` with constant `r(α)` in any extension where `s` splits; `Differential.rootSum_explicit`, `Liouville/RootSumExplicit.lean`), `frontIntegrate_valid`. Examples (`Mixed/FrontIntegrateExamples.lean`, `#guard`): `∫ x e^{x²} = ½ e^{x²}`, `∫ dx/(x log x) = log log x`, `∫ 2 log x/(x(log² x − 2)) = ∑_{a²=2} log(log x − a)`, `∫ e^{eˣ} eˣ = e^{eˣ}`, `∫ dx/(x² + 1) = ∑_{a²+1=0} log(x − a)/(2a)`. **The base part** is explicit when the base curve is a line (base `ℚ(x)`: `baseRat`, `integrateRational`, `baseRat_spec`, `ratLog_explicit` in `Mixed/MTBaseLine.lean`); on any other curve the total decision returns its witness (`decideTotalW`, mirrored through `decideLogW`, `decideAutoFullW`, `stageNFW`, `decideLoopW`, `CertQ.runW`, `decideEnumW`, answering exactly as `decideTotal`: `decideTotalW_isSome`, `Torsion/CurveWit*.lean`): the number field `ℚ[g]/(M)`, the exact part `v = Wsol(cs)/R0` and the logarithms `cⱼ log (Wⱼ(x, y)/Qⱼ(x))`, with `f = v′ + ∑ cⱼ uⱼ′/uⱼ` proved for every realization of the curve and every embedding of the number field into the constants (`CurveWQ.valid`, `baseCurve_explicit` in `Mixed/MTBaseCurve.lean`); a witness found through a Möbius-transformed certificate is an antiderivative in the variables `X = 1/(x − e)`, `Y = y Xᵏ⁰` for the original derivation (`mob_curve`, `CurveWQ.validMob`, `baseCurve_explicit_mob`: valid on the transformed curve for the derivation rescaled by `dx/dX`, multiplied back) |
| **Antiderivatives for the algebraic (radical) deciders** | `kpSolve` (`Mixed/KPWit`), `keDecideCW` (`KEWit`), `kqDecideCW` (`KQWit`), `kxDecideCW` (`KXWit`), `kqmDecideCW` (`KQMWit`), `krDecideCW` (`KRWit`), `kyDecideCW` (`KYWit`), `kzDecideCW` (`KZWit`): each mirrors its decider and returns, with a `true` answer, the solution of the (parametric) Risch equation and the logarithmic columns | `…_isSome` (answers exactly as the decider) and `…_valid`: `∫ B θʲ = y θʲ` (`kp_antiderivative`, plain cases), or `∫ f = (y/q₀) θʲ + ∑ₖ (−qₖ/q₀) ∫ colₖ θʲ` (`prde_param_eqN`) with every column explicit: square roots `ρ (log(W₀ + W₁ Y) − ½ log N)`, `Y² = Â` (`SqCol.logs`, `colY_logDeriv`, `ke_param_antiderivative`, `kq_param_antiderivative`); `n`-th roots `∑_k (sʲ/n) ζ^{(n−j)k} log W(ζᵏ Y₀)` (`kr_col_logs`), and for number-field residues the images under each embedding of `N` (`ky_root_logs`; the coordinates by the Vandermonde system in the roots of `M`) — in any extension with the constants `√κ`, `ⁿ√κ`, `ζₙ` |
| **Antiderivatives for the non-Kummer deciders** (non-constant curves `θⁿ + ∑ aᵢ(t) θⁱ = 0`, several places at infinity — split or ramified — and above `t = 0`, logarithmic and exponential levels) | `nkInfVGW`, `nkInfVRW` (`Mixed/NKWitInfVG.lean`, `NKWitInfVR.lean`), `nkETVGW`, `nkETVRW`, `nkET0W`, `nkET0RW` (`Mixed/NKWitET.lean`): the trace part through `elMW`, the exact part through witness mirrors of the whole exact-part pipeline — the system solution `(e, Z)` with common denominator `D` gives `Yᵢ = Zᵢ/(e₀ D)`, `cᵢ = −eᵢ₊₁/e₀` (`exactWLEW`, `Mixed/NKExactWit.lean`), rescaled by `t^{−rᵢ}` (`exactWRSLW`, `exactWREVLSW`) and moved to the power basis `Yθₖ = ∑ᵢ Yᵢ Tᵢₖ` (`exactTLVGW`, `exactTLEVGW`) — and the accepted candidate's units (`searchPW`, generic, `Mixed/NKSearchW.lean`) | `nk_integrateInfVGPW`, `nk_integrateInfVRPW`, `nk_integrateETInfVGPW`, `nk_integrateETInfVRPW`, `nk_integrateETInf0PW`, `nk_integrateETInf0RPW`, several slopes `nk_integrateInfVMRPW`, `nk_integrateETInfVMRPW` (`Mixed/NKMultiRWit`), `nk_integrateETInf0MRPW` (`Mixed/NKMultiR0Wit`), with residue-free poles `nk_integrateInfVMRRPW`, `nk_integrateETInfVMRRPW` (`Mixed/NKMultiRRWit`), and for single places at infinity (and above `0`) `nk_integrateTV`, `nk_integrateTEV` (any coefficients), `nk_integrateTR`, `nk_integrateTRE` (constant curves; `Mixed/NKWitTV`, `NKWitTEV`, `NKWitTR`, `NKWitTRE` — the single-place tests are the parametric pipeline without parameters, `exactTV_eq`, `exactTEV_eq`, `exactTR_eq`; the rationally gauged `exactWRE` has its own mirror `exactWREW`): for every large bound the procedure answers, the answer is `some _` exactly when the integral is elementary, and then it carries a valid antiderivative of the trace part `τ` (`ValidW`) and units `uᵢ ≠ 0` (S-units `uᵢ t^{−jᵢ}` above `t = 0`) with `f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ` (`nk_explicit_core`, `NKExpl`). `elMW_validE` needs only `L` elementary over `F₀` (`isElementary_alg`: `L = Fₙ(θ)` with `θ` integral). With precomputed candidates first: `nk_integrateTRP`, `nk_integrateTREP` (`Mixed/NKWitP`, generic prefix `prefW`). Example (`Mixed/NKWitExamples`, `#guard`): over `t = log x`, `θ³ + tθ = t²`, the pipeline returns the exact part `Y = (0, 1, 0)` of `θ′`, i.e. `∫ θ′ = θ`. Residue-free finite poles: `nk_integrateTVR`, `nk_integrateTEVR` (single places, `Mixed/NKWitTVR`, `NKWitTEVR`; the constructive counterparts of `nk_decidesR`, `nk_decidesRE`); non-zero residues with a logarithm certificate: `nk_integrateTVC`, `nk_integrateTEVC`, `nk_integrateInfVMRC`, `nk_integrateETInfVMRC` (`Mixed/NKWitC`, `integrate_of_logs`). Places at infinity (or above `0`) that become rational after a change of base curve: `bc_integrates` (`Mixed/NKBCW`, generic: the witness is valid in a tower `T′` over the new base curve inside an algebraic extension `L′ ⊇ L`, where the translated codes take the original values) with instances `nk_integrateInfVMR_bc`, `nk_integrateETInfVMR_bc` (`Mixed/NKBCW`, `NKBCWE`), `nk_integrateETInfVGP_bc`, `nk_integrateETInfVRP_bc`, `nk_integrateETInf0P_bc`, `nk_integrateETInf0RP_bc` (`Mixed/NKBCW3`), `nk_integrateInfVGP_bc`, `nk_integrateInfVRP_bc` (`Mixed/NKBCW2`); the `indepC`/`indepWC` certificates are turned into the `…PW` hypothesis by `hli_of_indepC`, `hli_of_indepWC0` (`Mixed/NKIndepPW`, `NKIndepPW0`). Not yet constructive: the first NK deciders with supplied bases (`nk_decides`, `nk_decidesT`, `…E`, `…ET`, `…2`, `…ET2`, superseded by the constructive versions above), and `searchTVP` (precomputed candidates only). Units over `ℚ(α)` (constant curves): `nk_integrateRNTR`, `nk_integrateETRNTRE` (`Mixed/NKWitRNTR`, `NKWitTREL`; `exactTRL` is the parametric pipeline `exactTLS` (`exactTRL_eq`), and the exponential one gets a witness mirror with parameters, `exactTRELW_valid`), with the explicit form `NKExplRN`: `f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑_{p,i} e_{p,i} u_{p,i}′/u_{p,i}` for the conjugate units `u_{p,i} = U_p(αᵢ)` and `e = c · V(α)⁻¹` (`rn_explicit`) |

The height-two towers (primitive, exponential with polynomial argument, hyperexponential with
arbitrary `η`) are reachable through `Tower.Tower2Spec R` / `Tower.integrate2_decides`
(`Computable/Integrate2.lean`); all height-three towers above are reachable through one entry point: `Tower.Tower3Spec R`
describes the tower (fifteen shapes), `Tower3Spec.certs` are its executable side conditions,
`Tower3Spec.integrate3` dispatches, and `Tower.integrate3_decides` (`Computable/Integrate3.lean`)
states, for every shape with valid certificates and every `A / D` of the field,
`HasElementaryIntegral (A / D) ↔ integrate3 s A D = true` — over the concrete differential fields
`RatFunc (RatFunc (RatFunc R))` with `x′ = 1`, `t₁′ = s.w₂`, `t₂′ = s.w₃`.

All tower integrators accept an **arbitrary** element `A / D` of the field (only `D ≠ 0` is assumed)
and make no assumption on constants. Examples proved by kernel evaluation: `∫ dx / log x`,
`∫ e^{-x²} dx`, `∫ e^{1/x} dx`, `∫ log² x / (x + 1) dx` are not elementary; `∫ dx / (x (log² x + 1))`,
`∫ log² x dx` are.

The pipeline: Hermite reduction (generic, totally correct at every tower level whose relevant
primes are normal) → polynomial / Laurent part (recursive limited integration `primLoop`, resp. one
Risch differential equation `rdeRational` per power of `t`) → logarithmic part by a
**resultant-free Rothstein–Trager test** (`Differential.residueTest`, `GPoly.residueCheck`):
with `r s′ ≡ b (mod s)`, all residues of `b / s` are constants iff
`s ∣ r^κ ∂ₜs − ∂ₜr s^κ`. Necessity is `dvd_residueTest`, sufficiency
`hasElementaryIntegral_of_residueTest` (splitting field, `∑ r(α) log (t − α)`); no algebraic numbers
are needed at run time.

**Height three** is decided completely for two primitives: `Tower.integratePrim2` = Hermite
reduction at `t₂` over the computable field `R(x)(t₁)`, residue test, and the polynomial part
`CPoly.integratePrim2PolyGen` (one parametric limited-integration problem in `R(x)(t₁)` per power
of `t₂`, ending in the height-two integrator). Kernel-checked examples
(`Computable/IntegratePrim2Example.lean`): `∫ log x log (x+1)`, `∫ 1 / (log x log (x+1))`,
`∫ log (x+1) / log x` are not elementary; `∫ (log (x+1)/x + log x/(x+1))`,
`∫ 1 / ((x+1) log (x+1))` are.

**Nested logarithms** (`t₂′ = W = u′ / u ∈ R(x)(t₁)`): in-field integration in `R(x)(t₁)`
(`Tower.isDerivPrim`, complete over every constant extension — the certificate that `t₂` is a new
transcendental), limited integration with a parameter function having simple poles
(`Tower.limitedPrimW`: the simple parts must cancel, `r_G s_W = c r_W s_G`, by
`Differential.deriv_eq_poly_add_two_proper`), the loop `Tower.prim2LoopW`, and at level `0` the
observation that `c₀ u′ / u` is just one more logarithmic derivative. Kernel-checked
(`Computable/IntegrateNestedLogExample.lean`): `∫ log log x dx`, `∫ dx / log log x` are not
elementary; `∫ dx / (x log x log log x)`, `∫ log log x / x dx`, `∫ log log x / (x log x) dx` are.

**Non-elementary nested primitives** (`li x`-type): at level `0` the constant `c₀` of Liouville's
theorem is pinned down because the residue test is *affine* in `c₀`
(`Differential.dvd_residueTest_affine`, `Tower.nestedConst`, `Tower.nestedConst_complete`); then
`∫ ρ = c₀ t₂ + ∫ (ρ - c₀ W)` is handed to the height-two integrator. Kernel-checked
(`Computable/IntegrateLiExample.lean`): `∫ li x dx`, `∫ dx / li x` are not elementary over
`ℚ(x, log x, li x)`; `∫ li x / x dx`, `∫ dx / log² x`, `∫ li x / log x dx`, `∫ dx / (log x li x)` are.

**Mixed towers** (`t₂ = exp a` over `R(x)(t₁)`): the Risch differential equation over a primitive
extension, `Tower.rdePrim` — denominator by `Differential.rde_denominator_regular`, polynomial part
by top-coefficient recursion (`Tower.rde_poly_top`), each step one `rdeRational` over `R(x)`; sound
and complete (`rdePrim_complete`, uniqueness `eq_zero_of_rde_homogeneous`). Kernel-checked
(`Computable/IntegrateExpPrimExample.lean`): `∫ eˣ log x`, `∫ eˣ / log x`, `∫ log x / eˣ`,
`∫ eˣ / x` are not elementary over `ℚ(x, log x, eˣ)`; `∫ eˣ (log x + 1/x)`, `∫ eˣ/(eˣ+1)` are.

**Logarithms over an exponential** (`t₂′ = W = U′ / U ∈ R(x)(eᵃ)`): in-field integration in
`R(x)(eᵃ)` (`Tower.isDerivExp`, complete over every constant extension; `Tower.derivExpSol`
returns the antiderivative), limited integration with a parameter function
(`Tower.limitedExpW` / `Tower.limitedExpSol`: the constant is forced either by the proper parts,
`r_G s_W = c r_W s_G` (`Differential.deriv_eq_laurent_add_two_proper_exp`), by a parametric Risch
equation `y′ + (j − k) a′ y = Gⱼ − c Wⱼ` over `R(x)` (`CPoly.prdeRationalG`), or by rational limited
integration at the constant term), the loop `Tower.primExpLoopW`, and at level `0` the observation
that `c₀ U′ / U` is one more logarithmic derivative. Kernel-checked
(`Computable/IntegratePrimExpExample.lean`): `∫ log (eˣ + 1) dx`, `∫ dx / log (eˣ + 1)` are not
elementary; `∫ eˣ log (eˣ + 1) dx`, `∫ eˣ log (eˣ + 1) / (eˣ + 1) dx`,
`∫ eˣ / ((eˣ + 1) log (eˣ + 1)) dx` are.

**Non-elementary primitives over an exponential** (`t₂′ = W ∈ R(x)(eᵃ)`, the proper part of `W`
at `eᵃ` failing the residue test): the Liouville constant is again pinned down by the
residue-affine test (`Tower.nestedConstE`, `Tower.nestedConstE_complete`; the Laurent parts at
`eᵃ` are absorbed into the cofactor of `dvd_residueTest_mul`), a Laurent polynomial minus `c W`
has constant residues only for `c = 0` (`Tower.laurent_const_eq_zero`), and
`∫ ρ = c t₂ + ∫ (ρ - c W)` goes to `integrateExp`. Kernel-checked
(`Computable/IntegrateLiExpExample.lean`, `t₂ = ∫ dx / (eˣ + x)`): `∫ x t₂ dx`, `∫ dx / t₂` are
not elementary; `∫ t₂ dx = (x − 1) t₂ − x + log (eˣ + x)`, `∫ t₂ / (eˣ + x) dx` are.

Intermediate decided classes at height three (two independent primitives `t₁, t₂` over `R(x)`, e.g.
`log x`, `log (x + 1)`): `A ∈ R(x)[t₁]` viewed in `R(x)(t₁)(t₂)` (`CPoly.prim2Base_decides`) and
`A(t₁) · t₂` (`CPoly.integratePrim2Times_decides`) and, more generally, all polynomials
`∑ Aₖ(x, t₁) t₂ ^ k` with `Aₖ ∈ R(x)[t₁]` (`CPoly.integratePrim2Poly`,
`CPoly.integratePrim2Poly_decides`, both directions), simple poles at `t₂`
(`CPoly.prim2Residue_decides`) and their combination (`CPoly.prim2Full_decides`);
`CPoly.Prim2Example.log_mul_log_not_elementary` proves, by kernel computation, that
`∫ log x · log (x + 1) dx` is not elementary. With **arbitrary** coefficients `Aₖ ∈ R(x)(t₁)`:
`CPoly.integratePrim2PolyGen` / `CPoly.integratePrim2PolyGen_decides` (iff) decide `∑ Aₖ t₂ ^ k`,
and `CPoly.prim2BaseGen_decides` shows that every element of `R(x)(t₁)` viewed in the larger field
is decided by the height-two integrator.

## Command-line tool

`lake build rtb` produces `.lake/build/bin/rtb` (a few minutes the first time; start-up 0.06 s).
Formulas are arguments or lines of standard input; `--time` prints the time per formula.

```
$ rtb 'x*exp(x^2)' '1/log(x)' '1/(x*sqrt(log(x)))' 'sqrt(x^2+1)'
```

Each answer first echoes the integrand as it was understood, then `elementary` with the pieces of
the antiderivative, `not elementary`, or `no answer at this bound`.

| input | route | time (native, this machine) |
|---|---|---|
| rational functions, towers of `exp`/`log` over `ℚ(x)` | `integrateShowF` (`frontIntegrateF_valid`, `frontIntegrateF_none`) | 1–90 ms |
| one square root of an `exp`/`log` expression, any rational expression in it | `frontSqrtAutoShow` | ≈ 0.4 s |
| `sqrt` of a rational function of `x` whose squarefree part has degree ≤ 2 and a rational point (or square leading coefficient), also inside `exp`/`log` | Euler substitution to `ℚ(u)`, then the first route | 1–30 ms |
| `sqrt` of other rational functions of `x` (genus ≥ 1, conics without rational point) | base curve `y² = s(x)`, general-curve decider | **slow**: seconds to minutes, sometimes no answer |

Speed of the general-curve route: the compiled code of several functions is replaced, through
proved equalities (`@[csimp]`), by versions that share work — the rows of the linear system for
the exact part (`rowsFin_eq_rowsFinF`, `rowsInf_eq_rowsInfF`, `cols_eq_colsF`), Newton's iteration
for Puiseux expansions (`evalBT_eq_evalBTF`, `newtonT_eq_newtonTF`), the choice of primes
(`autoPairs_eq_autoPairsF`) — and irreducibility over `ℚ` first tries a certificate by factor
degrees modulo primes (`Computable/DegCert.lean`: distinct-degree factorisation, `primeSums_sound`;
`irredQ_eq_irredQF`, `findFactor_eq_findFactorF`) before the exhaustive Kronecker search. No
theorem changes: the logical definitions are the old ones.

`tests/integrals.txt` lists standard integrals with the expected answer; `scripts/bench.sh [limit]`
runs them (one process each) and reports answer, expected answer and time; `tests/baseline.txt` is
the last recorded run.

What is and is not verified here: the parser, the rewriting `√(p/q) = r√s/q` and the Euler
substitution are ordinary unverified code (the genus-zero substitutions are proved correct for the
decision in `Genus0AutoPt`/`Genus0AutoSq`, but the tool applies them to the expression itself);
the theorems apply to the echoed integrand. Not accepted yet: trigonometric functions (constants
are rational), `n`-th roots for `n > 2`, several different radicals, non-constant exponents.

## Theory

Liouville's theorem (logarithmic, exponential, algebraic steps; towers; strong form with constant
field extension), structure theorems for primitive and exponential monomials (including Laurent
polynomials), Hermite reduction in monomial extensions, residue criterion and its converse, RDE
criteria and denominator bounds over `C(x)`, limited integration over `C(x)`, transcendence criteria
for primitives and exponentials, closure of `HasElementaryIntegral` under sums.

**Elementary integrals persist and add** (`Elementary/CommonExt.lean`, standard axioms): two
elementary extensions of `F` need not visibly have a common extension, but
**`HasElementaryIntegral.over_ext`** shows that an elementary integral of `f` over `F` gives one
over *every* differential extension field `E ⊇ F` — by the strong Liouville theorem the integral
is `v + ∑ cᵢ log uᵢ` over `F(c₁, …, c_r)` for finitely many new constants, and constants can be
adjoined to `E` simultaneously (`exists_ext_adjoin_const`: a transcendental one as the new
constant `X` of `E(X)`, an algebraic one in a finite extension; `exists_ext_adjoin_consts`). Hence
`HasElementaryIntegral.hasElementaryIntegralIn` (the extension-stable form `HasElementaryIntegralIn`
used throughout is *equivalent* to `HasElementaryIntegral`, `hasElementaryIntegralIn_iff`) and
**`HasElementaryIntegral.add`**, `.sub`, `.sum`, `hasElementaryIntegral_add_iff_left`: sums of
elementarily integrable functions are elementarily integrable, with no hypothesis beyond
characteristic `0` (`.const_mul`, `.linear` for constant coefficients;
`hasElementaryIntegral_elementary_iff`: integrability over `F` and over any elementary extension
of `F` are the same). **The constants do not matter** (`Elementary/ConstExt.lean`):
`hasElementaryIntegral_of_liouvilleIn_constField` is the converse of the strong Liouville theorem
(a Liouville form over `F(Const K)` in *any* differential field `K ⊇ F` gives an elementary
integral over `F`; adjoining finitely many constants is an elementary tower, a constant being a
logarithm of `1`), so Liouville's theorem is an equivalence (`hasElementaryIntegral_iff_liouvilleIn`),
and **`hasElementaryIntegral_constGen_iff`**: if `E ⊇ F` is generated over `F` by constants, `∫ f`
is elementary over `E` iff it is over `F` — the field of constants may be enlarged or shrunk
freely.

**Local expansions on superelliptic curves** (`Algebraic/Super*.lean`, standard axioms): for
`yⁿ = p(x)` (`p` squarefree, `gcd(n, deg p) = 1`) over constants `C`, ring embeddings of
`C⟮x⟯⟮y⟯` into Laurent series `K⸨s⸩` (`K` algebraically closed) at every place — ordinary points
(`embXY`, `x = α + s`, `y` = Hensel `n`-th root), branch points (`embB`, `x = e + sⁿ`,
`y = s U(s)`), infinity (`embI`, `x = s⁻ⁿ`, `y = s⁻ᵈ W(s)`); orders `ordAt`/`ordInf` (independent of
the chosen branch), a valuation on each (`SuperOrd`); derivations become
`(dX̂/ds)⁻¹ d/ds` (`embG_derivG`), so the residue of a Liouville form `v′ + ∑ cᵢ uᵢ′/uᵢ` at any
place is `∑ cᵢ ord uᵢ` (`res_liouville`, `res_liouville_branch`, `res_liouville_inf`);
conjugations `y ↦ ζy`, Fourier inversion, the norm, and the **degree theorem**
(`degree_le'`, `degree_eq'`: finite zeros of an integral function = its pole order at infinity,
via base change to `K(x, y)` so no roots of unity are needed in `C`); **integral closure**
`integral_of_regular'` (no finite poles ⇒ `∑ Pᵢ(x) yⁱ`), `const_of_ordAt_zero`;
**Abel's direction** `super_abel` (from a Liouville form with residues `r(Q)` and `ℚ`-linear `Λ`,
a multiple of the residue divisor becomes principal, witnessed by an integral function —
`abel_core`, `IsPrincipalS`); **residue-free Liouville forms are exact** (`super_second_kind`).

## Infrastructure for general towers

* Computable towers of any height (`Tower.Code`, `Tower.level`), generic polynomial arithmetic, gcd,
  Bézout, Hermite reduction (with completeness) and the residue test over any computable model
  (`COps` / `CField`).
* Models over **extended constants**: `CField.ofHom`, `CField.monomialIn`, `CField.mapHom`,
  `GFrac.semIn_mapHom`, `GPoly.hermiteCheck_sound_in` — the generic algorithms are correct in every
  fraction-field model, which is what the non-elementarity proofs need (the constants of the
  hypothetical elementary extension are adjoined first).
* Parametric problems over `R(x)`: verified linear solver (`CPoly.linSolve`), limited integration
  with several parameters (`CPoly.limitedCritN`), limited integration inside `R(x)(t₁)` for general
  elements (`Tower.limitedPrimGen`, sound and complete), the general `t₂`-loop
  (`Tower.prim2LoopGen`) with `CPoly.not_hasElementaryIntegral_prim2PolyGen`.
* `CPoly.Model2.of`: the two-level model hypotheses from two executable certificates.
* The Risch differential equation over an exponential extension `R(x)(exp a)`
  (`Tower.rdeExp`, sound and complete: `RDE/ExponentialDenominator.lean`, `Computable/RDEExp*.lean`),
  with the independence certificate `Tower.expIndep` (`a′, b′` not proportional) and uniqueness
  `Tower.eq_zero_of_rde_homogeneous_exp`; kernel-checked (`Computable/IntegrateExpExpExample.lean`):
  `∫ e^{x²} eˣ dx`, `∫ e^{x²} dx` are not elementary over `ℚ(x, e^{x²}, eˣ)`, `∫ (2x+1) e^{x²} eˣ dx` is.
* The **parametric** Risch differential equation `y′ + g y = A₀ / D - c A₁ / D` over `R(x)` with one
  unknown constant `c` (`CPoly.prdeRationalG`, sound and complete over every constant extension:
  `Computable/PRDEPoly.lean`, `Computable/PRDERational.lean`) — the ingredient of a primitive on
  top of an exponential.
* For **any** nested primitive `t₂′ = W ∈ R(x)(t₁)` with non-zero Hermite remainder (including
  `li x`): the polynomial-part loop (`CPoly.not_elementary_prim2PolyW`,
  `Tower.prim2LoopW_antiderivative`) and the residue test at `t₂` (`CPoly.prim2ResidueW_decides`).

**Towards exponentials with arguments in the tower** (`t₂ = exp a`, `a ∈ K[t₁]` of positive
degree, e.g. `x^x = exp (x log x)`, `e^{eˣ}`): the Risch differential equation
`y′ + g y = A / D` with `deg_t₁ g ≥ 1` is the *non-cancellation* case — the coefficients of
`Y = y D` are determined from the top by division, with no lower-level equation.
`GPoly.rdeNC` is the generic executable solver (any tower level given by its `COps` and the
code of `t′`), `GPoly.rdeNC_sound` / `GPoly.rdeNC_complete` its correctness (assuming only
`deg P′ ≤ deg P`). `Differential.transcendental_exp_arg` and
`Differential.exp_arg_no_new_constants` (`RDE/ExpArgConstants.lean`) show that such a `t₂` is a
monomial with no new constants (degree count: `n a′` is never a logarithmic derivative).
The tower `R(x)(t₁)(exp a)`, `t₁` primitive, `a ∈ R(x)[t₁]` with `deg_{t₁} a′ ≥ 1`, is
decided by `Tower.integrateExpArgPrim` (`expSplit`, Hermite reduction at `exp a`, residue test,
one `rdeNC` per power of `exp a`, `integratePrim` at level `0`). Kernel-checked
(`Computable/IntegrateExpArgPrimExample.lean`): `∫ x^x dx`, `∫ x^x log x dx`, `∫ dx / x^x` are
not elementary; `∫ (1 + log x) x^x dx = x^x`, `∫ 2 (1 + log x) x^{2x} dx = x^{2x}` are.
Over an exponential `t₁ = exp a₁` the special prime `t₁` needs the denominator bound
`Differential.rde_denominator_exp_poly` (`RDE/ExponentialDenominatorPoly.lean`: for a
polynomial coefficient only its constant term `g₀` matters at `t₁`). A pole of order `r` above
that of the right-hand side needs `e′ + (g₀ − r a₁′) e = 0` to be solvable in `R(x)`, which forces
the polynomial part of `g₀` to be `r a₁′` (`RDE/HomogeneousPolyPart.lean`); `r` is read off the
leading coefficients (`Tower.specialBound`, using the `HasNatTest` structure on the constants —
integers must be recognisable), and `Tower.rdeNCExpB` solves with denominator `t₁^{max(m, r)} D₁`
(`rdeNCExpB_complete`). The tower `R(x)(eᵃ¹)(exp a)` is decided by
`Tower.integrateExpArgExp`; e.g. `∫ e^{-x} exp (eˣ + 2x) dx = e^{-2x} exp (eˣ + 2x)` is found
through a pole of order `2` at `eˣ` where the integrand has order `1`
(`Tower.ExpArgExpExamples2.run_cancel`). Kernel-checked (`Computable/IntegrateExpArgExpExample.lean`):
`∫ e^{eˣ} dx`, `∫ e^{-eˣ} dx`, `∫ e^{eˣ} / x dx` are not elementary; `∫ eˣ e^{eˣ} dx = e^{eˣ}`,
`∫ 2 eˣ e^{2eˣ} dx` are.

### Hyperexponentials with simple poles (weak normalisation)

For `t′ = η t` with `η = Gn / Gd ∈ R(x)` arbitrary, the Risch differential equations
`y′ + n η y = f` can cancel at a simple pole `p` of `η` whose residue is a positive integer, and at
infinity when `deg Gn + 1 = deg Gd` (Bronstein, §6.1). `RDE/RationalCoeffW.lean` proves the
denominator bound `y D E ∈ C[x]` with `E = ∏ gcd(S, r - k)^k` (`S` the product of the simple primes
of `Gd`, `r Gd′ ≡ Gn (mod S)` the residue polynomial, `k` over the natural roots of any polynomial
`μ` with `S ∣ μ(r)`), the pivot bound `k∞ = deg(D E) - lc Gn / lc Gd`, and that `y′ = c η y`
(`c ∈ ℤ ∖ {0}`) has only the zero solution when `η` is not a logarithmic derivative of a radical
(certified by a repeated factor of `Gd`, or `deg Gn ≥ deg Gd`, or a simple prime whose residue is
no rational root of `μ`). No resultants and no factorisation: `μ` is found as a linear dependency among
`1, r, r², … (mod S)` by a verified elimination (`CPoly.depend`, `CPoly.depend_spec`;
`CPoly.muCheck_findMu`: the check `S ∣ μ(r)`, `μ ≠ 0` always succeeds); the rational roots of `μ`
come from the rational root theorem
(`CPoly.HasRatRoots`, instance for `ℚ`). `CPoly.rdeRationalW` is the resulting solver (sound and
complete; `CPoly.prdeRationalW` its parametric version with one unknown constant),
`Tower.rdePrimW` the corresponding RDE over `R(x)(t₁)` with a rational coefficient
(`Computable/RDEPrimW.lean`, `RDEPrimWComplete.lean` — the ingredient for a general
hyperexponential on top of a primitive tower, not yet assembled), `Tower.integrateHyperexpW` the
integrator, and `Tower.exp_arctan_not_elementary`
(`Computable/IntegrateHyperexpW.lean`) the kernel-checked statement that `∫ exp (arctan x) dx` is
not elementary, `Tower.exp_arctan_div_elementary` that `∫ exp (arctan x) / (x² + 1) dx` is
(both kernel-checked); `∫ (x² + x + 1) exp (arctan x) / (x² + 1) dx = x exp (arctan x)` is found by
`#eval`.

## Mixed algebraic–transcendental towers (in progress)

`Mixed/`, standard axioms only. Towers of logarithms and exponentials over the function field of a
curve `F(x, y) = 0` over `ℚ`:

* **Computable function fields of curves** (`Computable/CAlgVia.lean`, `Computable/CurveModel.lean`):
  `CField.algVia` models any algebraic extension of a computable differential field (products and
  zero tests modulo the minimal polynomial, inverses by the extended Euclidean algorithm,
  `y′ = −P^D(y)/P_Y(y)`); `curveModel` is the model of `Kc(x, y)`.
* **The parametric Risch equation on a curve** (`Mixed/CurveRde*.lean`): `curveRde Fc h ws`
  returns a basis of the pairs `(β, z)` with `z′ + h′ z = ∑ βⱼ wⱼ`. It is proved sound
  (`curveRde_sound`) and complete over the constants (`curveRde_complete`). Completeness uses
  pole bounds along every branch (`rde_local_lowerBd`: the potential is a derivative, so the
  leading terms cannot cancel), the ansatz `z · discR · Q = W(x, y)` (`rde_ansatz`), and
  irreducibility of `F`.
* **Elementary integrals on curves are explicit Liouville forms** (`Mixed/CurveRosenlicht.lean`,
  `curve_liouvilleForm`). With algebraically closed constants, an elementary integral is
  `v′ + ∑ cᵢ uᵢ′/uᵢ` over `Kc(x, y)` itself. This comes from the certificates:
  `certExists_of_curve`, plus the positive answers of the curve decision, which build the form.
* **One exponential over an arbitrary base** (`Mixed/ExpGen.lean`). `expGen_decides` is the
  structure theorem for `F₀(t)`, `t = exp`, given a *lift* of the base into every elementary
  extension (`ExpLift`). For curves the lift is `curve_expLift`: the curve over the new constants
  (`curve_over_constants`); transcendence and descent of Risch solutions come from
  `curveRde_complete`.
* **Decision for one exponential over a curve** (`Mixed/ExpCurveMain.lean`,
  `integrateExpCurve_decides`). Examples, by `#eval` on `y² = x³ + 1`: `∫ eˣ/√(x³+1)` is not
  elementary, and `∫ (e^y)′` is.
* **One logarithm over an arbitrary base** (`Mixed/PrimGen.lean`): with a lift of the base,
  an elementary integral of `A(t) + b(t)/sd(t)` (`t′ = η`) forces the residue test
  (`residue_of_lift_prim`) and gives the coefficient recurrence `pⱼ′ + (j + 1) η pⱼ₊₁ = Aⱼ` in the
  lift, with `A₀ − η p₁` integrable (`poly_of_lift_prim`, `prim_sum_deriv`).
* **Decision for one logarithm over a curve** (`Mixed/LogCurveMain.lean`,
  `integrateLogCurve_decides`): `t = log u`, `u` in the function field. The algorithm
  `integrateLogCurve` runs Hermite reduction, the residue test, then the polynomial part top down
  (`primChain`: `Qⱼ′ + γ η = aⱼ − (j + 1) η Qⱼ₊₁`, each solved by `curveRde` with right-hand sides
  `[·, η]`; sound and complete, `primChain_sound`/`primChain_complete`, transferred to every
  elementary extension by `curve_primLift`), and decides the constant term `a₀ − η Q₁` by
  `decideTotal`. Examples by `#eval` on `y² = x³ + 1`, `t = log x`: `∫ 1/log x` and
  `∫ log x/√(x³+1)` are not elementary; `∫ 1/(x log x)`, `∫ log x / x` and `∫ (log x)²` are.
* **Towers of logarithms over a curve, any height** (`Mixed/LT*.lean`, `Curves.LT.elT_decides`).
  The tower is realized in any differential field (`LTower`, height `n`); the same codes are
  realized in every elementary extension over its constants (`exists_lift`) and, as the top of
  a sub-tower, inside every level (`exists_sub`). Transcendence of the generators transfers
  between any two realizations (`Tr_transfer`: completeness of the solver in one, soundness in
  the other). The solvers, each sound and complete for constant coefficients in every
  realization: constant relations `lrel` (`LCols_spec`; at the base, relations among curve
  values are relations among bivariate numerators by irreducibility of the curve), parametric
  exact integration `lex` (`lex_spec`, ported from towers over `ℚ(x)`: Hermite reduction, sums of
  proper fractions are not derivatives, the parametric polynomial problem), the
  limited-integration chain `lchain`, and elementary integration `elT` by induction on the height
  (`elT_step`): the constant term of level `m + 1` is decided at level `m` inside the field
  `F m`. Only single-integrand tests reach the curve: the free constant of the chain multiplies
  `uₘ′/uₘ`, which always has an elementary integral. Examples by `#eval` on `y² = x³ + 1`:
  `∫ 1/log x` (height 1) and `∫ 1/log log x` (height 2) are not elementary;
  `∫ 1/(x log x log log x)` (height 2) is. The transcendence of the generators is certified by
  computation: `ltCert` (no `ηₘ` has an antiderivative in `F m`, by `lex`) proves it
  (`LTower.Tr_of_cert`), and `elT_decides_cert` needs no transcendence hypothesis
  (`ltCert` holds for `log x, log log x` over `y² = x³ + 1`, by `#eval`).

* **Mixed towers of logarithms and exponentials over a curve, any height** (`Mixed/MT*.lean`,
  `Curves.MT.elM_decides`). The tower data is `ks : (m : ℕ) → KindC m` (`.prim ηₘ` or `.exp aₘ`,
  codes of level `m`) and `lv` (`vₘ` with `ηₘ = vₘ′/vₘ`), realized in any differential field
  (`MTower`, height `n`). The machinery of mixed towers over `ℚ(x)` (`Computable/NestX*.lean`) is
  ported to the curve (mostly mechanically: codes `LC m`, operations `MO`): constant relations
  `mrel`, the parametric Risch equation `prdeC` for `f = h′ + ∑ cⱼ wⱼ′/wⱼ` (exponential level:
  special denominator bound through the logarithmic-derivative bound `pldC`, degree bound,
  coefficient loop; logarithmic level: degree bound through limited integration one level down)
  and parametric limited integration `paramLimC`. New at the base: `curveRdeL`, the Risch
  equation on the curve with potential `h′ + ∑ cⱼ uⱼ′/uⱼ` (`cⱼ ∈ ℚ`: the local bound at a branch
  loses at most `|residue|`, so the `x`-denominator of the ansatz is enlarged by
  `∏ (Qⱼ Q′ⱼ)^⌈|cⱼ|⌉`, `Qⱼ, Q′ⱼ` the `x`-denominators of `uⱼ` and `uⱼ⁻¹`; sound and complete over
  any constant field), and the structure theorem on the curve (`logsum_const_gen`: `Z′ = ∑ c u′/u`
  with `Z` in the function field forces `Z` constant — a function without poles is algebraic over
  the constants, `algebraic_of_noPoles`). The computable certificate `certC` proves, in every
  realization, the structure-theorem hypotheses (transcendence, no new constants, `ηₘ = vₘ′/vₘ`).
  `mspecs`: `prdeC` and `paramLimC` are sound and complete at every certified level
  (`MTSpecs.lean`). Elementary integration `elM` (`MTElem.lean`) then goes by induction on the
  height: a logarithmic level as for log towers (chain `mchain` on `paramLimC`); an exponential
  level by the generic one-exponential theorem `expGen_decides` with the lift property
  `MTower.expLift` (in every elementary extension, the realization over its constants; a
  solution there of a Risch equation with code data descends by completeness of `prdeC` there and
  soundness in `L`). Examples by `#eval` on `y² = x³ + 1`, `t₀ = eˣ`, `t₁ = log(eˣ + 1)`: the
  certificate holds; `∫ eˣ √(x³+1)` is not elementary (11 s), `∫ (eˣ √(x³+1))′` is; at height 2,
  `∫ log(eˣ + 1) · eˣ/(eˣ + 1)` is elementary and `∫ log(eˣ + 1)` is not (5 min for both).

**Scope.** Every sub-problem of the recursion is a single-integrand question at the base or a
linear-algebra question (relations, Risch equations, limited integration) that is solved exactly.
For an exponential level the constant term is a single integrand; for a logarithm `tₘ` the free
constant of the chain multiplies `ηₘ = vₘ′/vₘ`, which always has an elementary integral. So the
parametric elementary problem "which constant vectors `c` make `∑ cⱼ wⱼ` elementary", which on a
curve of genus ≥ 1 would need ℚ-linear relations among divisor classes in the Jacobian modulo
torsion (Mordell–Weil ⊗ ℚ, Néron–Tate heights), never arises for these towers. It is not decided
here (it is not needed by the algorithm).

**Algebraic functions of one logarithm or exponential** (`Mixed/MTRescale.lean`,
`elM_decides_rescaled`): with `u` a new base variable (`∫ f dx = ∫ (f/u′) du`, invariance of
elementary integrability under rescaling the derivation), an algebraic function of `u` becomes
part of the base curve and `x` becomes `exp u` or `log u`. Example by `#eval`: `∫ √(log x) dx`
(curve `w² = u`, `x = exp u`, integrand `w · x`) is not elementary; `∫ (x √(log x))′ dx` is
(16 s for both).

**Kummer radicals over a logarithmic level — the first genuinely mixed case**
(`Mixed/KP*.lean`, `Curves.MT.MTower.kp_decides`). Over a certified mixed tower whose top level
`t` is logarithmic, with `θⁿ = a(t)`, `a ∈ Fₘ[t]` squarefree of degree prime to `n` (both checked on
the codes), `∫ B(t) θʲ` (`B ∈ Fₘ[t]`, `0 < j < n`) is elementary iff the Risch equation
`y′ + (j/n)(a′/a) y = B` has a solution at the top level (`kpDecide`, through `prdeC` with the
logarithmic potential `(j/n, a)`), over any constants. This is a curve `yⁿ = p(x)` over a
*differential* base (`x′ = η ∈ Fₘ`): the superelliptic embeddings are reused, with the Laurent
derivation `δ + s d/dX` (`KPLaurent`: coefficient derivation; `KPEmbed`: the embeddings are
differential; `s = η − α′` at an ordinary point, `(η − e′)/n · X^{1−n}` at a branch point, non-zero
because `η` has no antiderivative, not even an algebraic one, `not_deriv_of_integral`). The residue
of a Liouville form vanishes where the integrand has no pole (`residue_eq_zero`), so the
logarithms have no zeros or poles and lie in the base (`logs_in_base`), and the `yʲ`-coordinate of
`v` is an antiderivative (`kp_liouville`). Examples by `#eval` (3 s): `∫ √(x + log x)` and
`∫ √(log x)` are not elementary; `∫ √(log x)/x` and `∫ (3/2)(1 + 1/x) √(x + log x)` are.
**Denominators `a(t)ᵏ`** (`kp_decides_pow`, `kpDecideK`): at the branch points the integrand may
then have poles, and the residue argument runs on the part with exponents divisible by `n`
(`KPClass`: the substitution `X ↦ ζX` commutes with the local derivation; `KPBranchClass`: the
expansion of `y` at a branch point is `X·U(Xⁿ)`, by uniqueness of `n`-th roots, so `b yʲ` has no
such part). Examples (50 s): `∫ dx/√(x + log x)` is not elementary; `∫ (1 + 1/x)/(2√(x + log x))`
and `∫ dx/(x √(log x))` are. **General integrands in `θ`** (`Mixed/KLProj.lean`,
`KLDecide.lean`, `kl_iff`, `kl_decides`): `∫ (g₀ + ∑_{0<j<n} Bⱼ(t)/a(t)^{kⱼ} θʲ)` (`g₀` any element
of the tower field) is elementary iff `∫ g₀` is (decided by `elM`, through the invariance under the
algebraic extension `Fₘ₊₁(θ)`) and every `kpDecideK` answers `true`. The `⇒` direction is a Galois
projection: after adjoining a primitive `n`-th root of unity (a finite, hence elementary, step),
the automorphisms `θ ↦ ζᵏθ` commute with the derivation, and averaging a Liouville form against
`ζ^{−jk}` gives a Liouville form for the `θʲ`-component (`proj_liouville`, `kl_components`).
Not treated yet: other denominators (poles at the ordinary places,
where logarithmic parts appear), an exponential base (the places over `t = 0` split:
`∫ √(1 + eˣ)` has a logarithmic part), and general algebraic `θ` over a transcendental level.
Towers with dependent data (`exp(x/2)` over `exp x`) fail `certC` and must be rewritten.

**Square roots over an exponential level, with logarithmic parts** (`Mixed/KW*.lean`,
`Mixed/KE*.lean`, `Curves.MT.MTower.keDecide_correct`). The top level `t` is an exponential
(`t′ = a′t`), `θ² = A(t)` with `A` squarefree of odd degree and `A(0) ≠ 0`, and the integrand is
`B(t) θ / (tᵏ A(t)ˡ)` (poles at the branch points are handled by the class argument of `KPClass`,
ported to `x′ = ω(x)` in `KWClass`). Here the logarithmic part can be non-trivial (`∫ √(1 + eˣ) = 2√(1 + eˣ) +
log((√(1 + eˣ) − 1)/(√(1 + eˣ) + 1))`). The local theory of `KP` is redone for `x′ = ω(x)` (`KWEmbed`,
`KWMain`, `KWExact`): the logarithms have no zeros or poles over `t ≠ 0` (no algebraic
`α′ = ηα`, `not_exp_of_integral`), so their divisors lie on `P± = (0, ±√A(0))` and `∞`
(`KELiouville`). If `A(0)` is not a constant times a square in `Fₘ`, `P₊ − ∞` is not torsion
(`nontors_of_nonsquare`) and there is no logarithmic part. Otherwise, after normalizing `θ̂ = θ z/√κ`
(so `P± = (0, ±1)` are rational over the code field), the logarithmic part is `c W′/W` for the
function `W` with divisor `N(P₊ − ∞)` when that class is torsion (`ke_liouville_tors`), and there is
none when it is not (`ke_liouville_nontors`). **Torsion is decided over the function field of the
codes** by the two-primes oracle of the superelliptic theory, which needs no new geometry: the code
fields are made computable Lean fields (`Computable/RatFuncC.lean`: `K(t)` with gcd-normalized
fractions; `Computable/NFK.lean`: `K[y]/(f)`; `Mixed/KECodes.lean`: `LC m → Kₘ` and back, with an
injective evaluation into any realization), and their reductions modulo `p` (`Mixed/KEReduce.lean`,
`Algebraic/SupRedRF.lean`, `SupRedNFK.lean`) are induced by embeddings into `ℚ_p` that send the
transcendentals to transcendental `p`-adic integers with prescribed residues (`ℤ_p` is uncountable,
`Algebraic/PadicTransc.lean`) and `y` to a Hensel root. The witness `W` then gives the extra column
`B_W` of a parametric Risch equation. `keDecide_correct`: **whenever `keDecide` answers, the answer is
correct** (standard axioms). It always answers when `A(0)` is not a constant times a square;
otherwise it answers when the torsion oracle does (its completeness over function fields, i.e.
that good primes and certificates always exist, is not yet proved). Examples (`KEExamples.lean`,
`#guard`, 4 s): `∫ √(1 + eˣ)`, `∫ eˣ√(1 + eˣ)`, `∫ √(1 + eˣ)/eˣ` and `∫ √(1 + e³ˣ)` (3-torsion on
`θ² = 1 + t³`), `∫ 1/√(1 + eˣ)` and `∫ eˣ/√(1 + eˣ)` are elementary; `∫ √(x + eˣ)`,
`∫ 1/√(x + eˣ)`, `∫ x√(1 + eˣ)` and `∫ √(1 + eˣ + e³ˣ)` (no torsion) are not. **General integrands** `g₀ + B(t) θ / tᵏ` (`g₀` any element of the tower field;
`Mixed/KEFull.lean`, `ke_full_decides`, also with `B(t)/(tᵏ A(t)ˡ)`): the `θ`-component is split off by the Galois projection,
ported to `x′ = ω(x)` (`KWProj`, `kl_componentsW`, valid for a top level of either kind), `g₀` is
decided by `elM` and the rest by `keDecide`.

**Square roots over a logarithmic level with poles at ordinary places** (`Mixed/KQ*.lean`,
`Curves.MT.MTower.kqDecide_correct`). The top level `t` is a logarithm (`t′ = η`), `θ² = A(t)`
(`A` squarefree of odd degree) and the integrand is `B(t) θ / (D(t) A(t)ˡ)` with
`D = ∏_q (t − c_q)`, the `c_q ∈ Fₘ` given as codes (distinct, `A(c_q) ≠ 0`, `B(c_q) ≠ 0`, checked).
The poles of the integrand at the ordinary points `(c_q, ±√A(c_q))` force logarithmic parts. New
local theory: **the residue formula at a simple pole** for the derivation `δ + s d/dX`
(`KQLocal`: `(∑ κᵢ ord Uᵢ) s₀ = F₋₁`; a pole of `V` would propagate below `−1`) and the expansion of
`b y` at a pole of `b` (`KQExpand`). `KQLiouville`: the residues `ρ_q = r_q √A(c_q)/(η − c_q′)` must be
constants (`kq_resid_const`; the algorithm tests that `Q_q = ρ_q²` has derivative `0`, else **not
elementary**), and when they all lie in one class `ℚ √s`, each logarithm has divisor `λ_j Δ`,
`Δ = ∑ m_q ((c_q, β_q) − (c_q, −β_q))` (`kq_core`), so: if `Γ = ∑ m_q (c_q, β_q)` is not torsion there is
no Liouville form (`kq_liouville_nontors`), and if `W = W₀ + W₁y` has divisor `N Γ − (N deg Γ)∞`,
then `b y = (a y)′ + e B_W y` (`kq_liouville_tors`). Over the codes the points are rational after
the twist `ỹ = √s θ` (`ỹ² = s A`), so torsion is decided by the function-field oracle of the
exponential case, for several points (`KQBridge`: `not_isPrincipalS_gen`, `ordAt_witW_gen`).
`kqDecide_correct` (standard axioms): **whenever `kqDecide` answers, the answer is correct**.
**Residues in several classes** (`Mixed/KQM*.lean`, `Curves.MT.MTower.kqmDecide_correct`, which
supersedes `kqDecide`): the squared residues `κ_q ∈ ℚ` are written `c_q² ∏_{i ∈ T_q} gᵢ` over greedily
chosen generators `gᵢ` that are multiplicatively independent modulo squares (`KQMCodes`: `gensOf`,
decided exactly by `inGB`, with `qsqrt_sq` the completeness of the rational square root). New
algebra (`Algebraic/SqrtIndep.lean`, not in Mathlib): **in any field of characteristic `0`, the
`2ᵏ` products of square roots of multiplicatively independent rationals are `ℚ`-linearly independent**
(`prods_indep`, via `mem_closure_insert`: elements of `F(y)`, `y² ∈ F`, are `u + v y`). So the class
values `∏_{i ∈ T} √gᵢ` are independent (`prodRoots_indep`), a separating `ℚ`-linear functional exists
(`exists_sep_functional`), and the Liouville form splits by class (`KQMulti`: `kqm_core`,
`kqm_liouville_nontors`, `kqm_liouville_tors`, with `kqm_log_gen` for logarithms with
proportional divisors). Each class is tested on its own twist `ỹ² = s_T A` over the code field and
read back on `y² = A` (`KQTwist`: `vanishAtN_scale`, `principalMulN_scale`; `KQMBridge`:
`class_not_principal`, `class_witness`); the answer is the parametric Risch equation with one
column per class. `kqmDecide` answers whenever the per-class torsion oracles do. Examples
(`KQMExamples.lean`, `#guard`, 5 s): `∫ √(log x)/(x(log x − 1)(log x − 2))` (classes `ℚ` and
`ℚ√2`) is elementary; `∫ √(log³x + 1)/(x log x (log x − 1))` is not (the `√2`-class point is not
torsion). Examples
(`KQExamples.lean`, `#guard`): `∫ (1 − 2 log x)/(√(log x)(log x − x²))` (=
`log((√(log x) − x)/(√(log x) + x))`, a pole at `log x = x²`) and `∫ √(log³x + 1)/(x log x)` (3-torsion
on `θ² = t³ + 1`) are elementary; `∫ √(log x)/(log x − 1)` (residue `x`),
`∫ (1 − 2x²)/x² · √(log x)/(log x − x²)` and `∫ √(log³x + log x + 1)/(x log x)` (no torsion) are not.
**Code reduction** (`Computable/GReduce.lean`, `Mixed/MTRed.lean`): the log-level Risch solver
`prdePrimC` now reduces (by a checked gcd division, `redFrac`, value preserved: `ev_redL`) the
columns it passes one level down; without it the unreduced fractions (`x¹⁶/x¹⁷`) made the
genus-1 examples run for more than 10 minutes, with it the coefficient loop takes under a second
(`RdeSpecK.map_input` transports the specification). Moreover the operations on the base codes
`ℚ(x)` now reduce every fraction by its gcd (`xOpsR`, `COps.normalizeBy` with `redFrac`, the model
`xModel` unchanged in value), which speeds up every algorithm on curves.
**Ordinary poles over an exponential level** (`Mixed/KX*.lean`,
`Curves.MT.MTower.kxDecide_correct`, standard axioms): `∫ B(t) θ/(tᵏ ∏ (t − c_q) A(t)ˡ)` with
`t = e^g`, `θ² = A(t)`, poles at `c_q ≠ 0` whose residues lie in any number of classes `ℚ√s`. At
`t = 0` the residues say nothing (`α′ = η α` has the solution `α = 0`), so the logarithms may carry
a multiple of `δ₀ = P₊ − P₋` (`P± = (0, ±√A(0))`). The abstract theory (`KXPrep`, `KXMulti`,
`KXExp`, `KXExp2`) normalizes each logarithm to `w² x^{−(r+s)}`, whose divisor is
`∑ 2λ_k Δ_k + (r − s) δ₀` (`kxe_norm`), and splits into three cases: `√A(0) ∉ Fₘ` forces `r = s`
(`KXSym.ordAt_pm`: the two branches over `x = 0` are conjugate, `kxe_mu0_sym`); `P₊ − ∞` torsion
with witness `W₀` kills `δ₀` (`kxe_kill_W0`) and adds one column (`kxe_tors_W0`); `P₊ − ∞` not
torsion forces `r = s` when every class is torsion (`kxe_mu0_nt`). Then a non-torsion class with a
non-zero residue leaves no Liouville form (`kxe_nontors`), and with all classes torsion
`b y = (a y)′ + ∑ e_i B_i y` (`kxe_tors_mu0`, `kxe_tors_W0`). The algorithm `kxDecide` (`KXCodes`)
tests constancy of the squared residues `B(c)²A(c)/((η c − c′) R)²`, the classes, the torsion of
each class and of `P₊ − ∞` (on the twist `(z/√κ)² A`, `κ = z² A(0)`), and solves the parametric
Risch equation. It answers `none` only when a torsion oracle gives no answer within its bounds or
when some class and `P₊ − ∞` are both non-torsion (then a relation between them in the
Mordell–Weil group decides: independence certificates `kxDecideMW…` and the relation search
`kxDecideD`, see the Mordell–Weil section). Examples (`KXExamples.lean`, `#guard`,
under 15 s): `∫ √(1 + eˣ)/(eˣ − 1)`, `∫ √(1 + eˣ)/((eˣ − 1)(eˣ − 3))` (two classes), `∫ √(2 + eˣ)/(eˣ − 1)`,
`∫ (eˣ(x − 2) − x)/((eˣ + x − x²)√(x + eˣ))` (`A(0) = x`, not a square) are elementary;
`∫ √(x + eˣ)/(eˣ − 1)`, `∫ √(1 + e³ˣ)/(eˣ − 1)` (non-torsion class) and `∫ √(1 + e³ˣ)/(eˣ − 2)` are
not. Performance note: on `θ² = 1 + t + t³` the per-class torsion oracle with primes `5, …, 37`
did not finish in 150 s (with `17, 19, 23` it answers at once); the oracle is shared infrastructure.
Not treated: poles over irreducible factors of `D` of degree `> 1`, ordinary poles for `n > 2`
(the radicals of higher order below have no poles away from `t = 0` and the zeros of `A`), and
the Mordell–Weil relation case above.


**Radicals of any order over an exponential level** (`Mixed/KR*.lean`, `Algebraic/Ramanujan.lean`,
`Algebraic/KRDft.lean`, `Curves.MT.MTower.krDecide_correct`, standard axioms):
`∫ B(t) θʲ/(tᵏ A(t)ˡ)` with `t = e^g`, `θⁿ = A(t)` (`A` squarefree, `gcd(n, deg A) = 1`, `A(0) ≠ 0`,
`0 < j < n`, `gcd(j, n) = 1`). The logarithms of a Liouville form have zeros and poles only over
`x = 0` and `∞` (`kr_prep`); the automorphism `σ : y ↦ ζy` and the projection
`four j = ∑_k ζ^{k(n−j)} σ_k` (`KRFourier`) isolate the `yʲ`-part. At the points
`P_k = (0, ζᵏβ₀)` (`β₀ⁿ = A(0)`): if `β₀ ∉ Fₘ` a Galois automorphism shifts the `P_k` and the
projection of every logarithm vanishes (`galois_shift`, `four_dl_shift`); otherwise the divisor
`Ψ = ∑_k c_n(k) P_k` (Ramanujan sums, `ramC_eq`, `sum_ramC_mul_pow`) governs it: not torsion ⇒
the projections vanish (`four_dl_nontors`, a DFT argument `corr_core`); `N Ψ` principal with
witness `W₀` ⇒ every projection is a constant multiple of that of `W₀` (`four_dl_tors`), one
column. The algorithm `krDecide` (`KRCodes`) finds `z` with `zⁿ A(0) = κ ∈ ℚ` (a kernel of the Risch
solver), asks the torsion oracle about `Γ = ∑ (c_n(k) + M₀)(0, ζᵏ)` on the twist `(zⁿ/κ) A` over the
cyclotomic extension `Kₘ(ζ)` of the code field (`NFz`, `Φₙ` computed as `cycloQ`, `cycloQ_spec`),
builds the witness there, takes its norm `∏_{u ∈ (ℤ/n)ˣ} τ_u W` (checked to descend to `Kₘ`;
`kr_norm_witness`: divisor `φ(n) N Γ`), and computes the column `zʲ Dⱼ/g` by an extended gcd
modulo `Yⁿ − Â` over `K_{m+1}` (`krCol_spec`, `twist_dlog`). The column is elementary through the
identity `∑_k ζ^{(n−j)k} W(ζᵏỹ)′/W(ζᵏỹ) = n Dⱼ ỹʲ/g` (`twist_sum`, `kr_col_hei`, over an extension
with `ζ` and `ⁿ√κ`, `root_zeta_ext`). The oracle over `Kₘ(ζ)` needs `Φₙ` irreducible over `Kₘ`,
proved for the base `ℚ(x)` and any tower above it (`cycK_irr_linear`, Gauss's lemma and `t ↦ 0`).
It answers `none` only when the torsion oracle gives no answer within its bounds or a runtime
check on the witness fails. Examples (`KRExamples.lean`, `#guard`): `∫ ∛(1 + eˣ)` is elementary
(torsion path, about 2.5 min), `∫ x ∛(1 + eˣ)` is not (torsion path, the parametric equation
fails), `∫ ∛(x + eˣ)` is not (`A(0) = x` has no cube root in `ℚ(x)`); by
`#eval` (10 min, not in the build) `∫ ∛(1 + e²ˣ)` is elementary (the points over `t = 0` are the
2-torsion points of `t² = u³ − 1`).

**Radicals of any order with ordinary poles over an exponential level** (`Mixed/KY*.lean`,
`Curves.MT.MTower.kyDecide_correct`, standard axioms): `∫ B(t) θʲ/(tᵏ ∏_q (t − c_q) A(t)ˡ)` with
`t = e^g`, `θⁿ = A(t)` as above, and simple poles at distinct `c_q ∈ Fₘ`, `c_q ≠ 0`, `A(c_q) ≠ 0`.
The residue at `P_{q,k} = (c_q, ζᵏβ_q)` is `ρ_q (ζᵏβ_q)ʲ` with
`ρ_q = B(c_q)/((g′c_q − c_q′) R_q(c_q))` (`ky_prep0`, `ky_resid_const`). It must be constant, so
`κ_q = ρ_qⁿ A(c_q)ʲ ∈ ℚ` (`kyConst`); otherwise the integral is not elementary
(`ky_forward_const`). The caller supplies a number field `N = ℚ[X]/(M)` with a primitive `n`-th
root of unity `ζ` and elements `γ_q` with `γ_qⁿ = κ_q`, all checked at runtime (`kyFieldOK`;
irreducibility of `M` over the code fields is a `Fact`, proved for the base `ℚ(x)` by
`liftQ_irr_linear`). Then `β_q = (γ_q/ρ_q)^a A(c_q)^b` with `aj + bn = 1` (`kummer_root`), and the
residues are ℚ-combinations of a power basis of `N`. By duality (`exists_comb`), the orders of the
logarithms at the poles are rational combinations of the components `D_f` (the coordinates of
`ζ^{kj}γ_q`, `ky_orders`). Each component goes to the torsion oracle over `Kₘ ⊗ N` (`NFM`,
`redAtNFM`).

* **All components torsion.** The witnesses give columns. Their coordinates are computed by an
  extended gcd over `K_{m+1} ⊗ N` (`kyColM`, `kyColM_spec`).
* **The fibre over `t = 0`.** It is handled as in `krDecide`, but over `Kₘ ⊗ N` and without a norm
  (`ky_zfacts`, `ky_hnt`, `ky_psi_wit`).
* **The parametric Risch equation** with all the columns then decides (`ky_forward_pos`,
  `ky_backward`).

The columns are elementary. Each embedding of `N` (a root of `M` in a splitting extension,
`split_ext`) turns a column into `(sʲ/n) ∑_k ζ^{(n−j)k} W(ζᵏỹ)′/W(ζᵏỹ)` (`ky_root_hei`). The
coordinates are recovered by inverting the Vandermonde matrix of the roots over the constant
subfield (`vandermonde_const`, `ky_col_hei`).

A component that is not torsion makes the integral non-elementary (`ky_nontors`,
`ky_forward_neg`) whenever the orders over `t = 0` can be killed. That happens in two cases:

* `A(0)` has no `ℓ`-th root in `Fₘ` for any prime `ℓ ∣ n` (full Galois orbit, `galois_full`,
  `kill_full`);
* every point `(0, ζᵏβ₀)` of the twist is torsion (`kyZeroTors`, `kill_tors`).

Otherwise `kyDecide` answers `none`. That remaining case is a non-torsion component together with
a non-torsion fibre over `t = 0`, a Mordell–Weil relation question.

Examples (`KYExamples.lean`, with `N = ℚ(ζ₃)`):

* `#guard`, about 4 s: `∫ ∛(1 + eˣ)/(eˣ − x)` is not elementary (the residue is not constant).
* `#eval`, about 15 min each, not in the build:
  * `∫ 7∛(1 + eˣ)/(eˣ − 7)` is elementary;
  * `∫ (7 + x(eˣ − 7)) ∛(1 + eˣ)/(eˣ − 7)` is not.

**Pole factors that split over a number field** (`Mixed/KZ*.lean`,
`Curves.MT.MTower.kzDecide_correct`, standard axioms). This is the same setting as `kyDecide`,
but with a denominator `D(t) ∈ Fₘ[t]` whose roots `c_q` lie in `Kₘ ⊗ N` rather than in `Fₘ`. An
example is `D = e²ˣ + 1`, with poles `±i`. The poles are given by their coordinates, and
`D = ∏ (t − c_q)` is checked over `Kₘ ⊗ N` (`kzOK`, `nfmProd`).

The following are computed in `Kₘ ⊗ N`:

* the residues `ρ_q = B(c_q)/((η c_q − c_q′) R_q)`;
* their constancy, with the derivation acting on the coordinates (`nfmD`, `psi_nfmD`);
* `κ_q ∈ N`, whose coordinates must be rational (`kzK`, `kzConst_spec`);
* the points (`kzBeta`).

The rest is `kyDecide`'s: the components, the torsion oracle over `Kₘ ⊗ N`, the fibre over
`t = 0` and the columns.

The proofs reuse the abstract theory unchanged, because after the lift (`ky_lift`) a root of `M`
is a constant, so it lies in every level. The poles `ψ c_q` then belong to `Fₘ` (`kz_data`,
`kz_points`, `kz_forward_pos/neg/const`, `kzDecide_correct`). Irreducible factors whose roots
generate a non-constant extension (such as `t² − x`) are not covered.

Examples (`KZExamples.lean`, `#guard`), over `t = e²ˣ` with `N = ℚ(i)` and poles `±i`:

* `∫ √(e²ˣ + 3/4)/(e²ˣ + 1)` is elementary (about 80 s).
* `∫ x √(e²ˣ + 3/4)/(e²ˣ + 1)` is not: the residues are not constant.
* `∫ (1 + x(e⁴ˣ + 1)) √(e²ˣ + 3/4)/(e²ˣ + 1)` is not: the residues are the same, but the parametric
  equation has no solution (about 80 s).

The common denominator of a component's coordinates (`kyDen`) is a least common multiple, not a
product. With a product, the divisor multiplicities blow up: here one oracle call went from over
300 s to 5 s after the change.

**Changing the base curve** (`Mixed/KB*.lean`, `Curves.MT.MTower.kzDecide_bc_correct`, standard
axioms). This handles pole factors whose roots generate a non-constant extension of the base field
`F₀` of the tower, such as `t² − x` over `ℚ(x)`. The base is changed once and the whole tower is
translated, so the pole factor may sit at any level `m`. For example, `t₁² − x` with `t₁ = log x`
above `t₀ = eˣ` is covered. The base curve is changed to a curve `Fc'(x, w) = 0`
over which the factor splits (here `w² = x`, poles `±w`).

The user gives:

* the new curve `Fc'`;
* the old `y` as a code `Yc` on it;
* the minimal polynomial `Q` of `w` over the old base field.

Two identities are checked in `K₀[W]/(Q)`: `Fc'(x, W) = 0` and `Yc(x, W) = y` (`bcOK`). Codes of every
level are translated (`tauC`, `tauK`, `tau_evL`). For any root `w'` of `Q`, the field `L' = L(w')`
carries a realization of the translated tower over the new base curve, with the same values
(`base_change`).

The irreducibility of `Fc'` over the constants of `L'`, which may be larger than those of `L`, is
required as geometric irreducibility (`GeomIrr`: irreducible over `K[x]` for every field `K ⊇ ℚ`).
It has two certificates:

* Eisenstein's criterion at some `x = c` (`eisC`, `eis_irr`);
* Eisenstein at a squarefree `p(x)`, with Bezout certificates `a p + b p′ = 1` and `c p + e r = 1`,
  where `r = a₀/p` (`eisPC`, `eisP_irr`). The argument works at a prime factor of `p` over `K`.
  This covers, for example, `w² = x² + 1`.

The minimality of the root then follows (`curve_irr`). Eisenstein's criterion also gives the `Fact`s
over the code fields (`fKc_irr_eis`, `qK_irr_linear`).

Elementary integrability is invariant under the algebraic extension `L ⊆ L'`, so `kzDecide` over
the new tower decides the original integral. Pole factors whose roots are algebraic over a transcendental level
and not over `F₀` are not covered, for example `√(x + eˣ)` as a root of `t₁² − x − t₀`.

Examples (`KBExamples.lean`), over `t = eˣ` with base `ℚ(x)`, `A = (t + 1)(t² − x) + 1` and poles
at the roots `±√x` of `e²ˣ − x`. The new base is `w² = x`, and every `Fact` is proved from
Eisenstein's criterion.

* `#guard`: the base-change checks hold.
* `#guard`: `∫ √A(eˣ)/(e²ˣ − x)` is not elementary, because its residue is not constant.
* `#eval` (about 10 min, not in the build): `∫ (2x − 1)√A(eˣ)/(e²ˣ − x)` is not elementary. Its
  residues are constant, but the residue component is not torsion and `A(0) = 1 − x` has no
  square root.

**Any constant field** (`Elementary/AlgDescent.lean`, `AlgDeriv.lean`, `AlgBase.lean`). The
decision on the curve (`decideTotal_decides`) needs algebraically closed constants. That
restriction is removed by a general theorem: **elementary integrability is invariant under
algebraic extensions of the base**, finite or not (`hasElementaryIntegral_isAlgebraic_iff`,
`HasElementaryIntegralIn.of_isAlgebraic`). Descent is a finite-support argument (an elementary
tower over `K` only uses finitely many elements of `K`, which are algebraic over `F` and can be
adjoined first). Ascent puts `K` and an elementary extension `E` in the algebraic closure of
`E`, whose derivation is built here (`algDifferential`: the formula `z′ = −p^D(z)/p′(z)` is a
derivation because it agrees with Mathlib's derivation on every finite subextension). With
`isAlgClosed_constants` (the constants of an algebraically closed differential field are
algebraically closed), `elM_decides_any` lifts any realization to the algebraic closure, decides
there, and transfers the answer back.

## Decided algebraic classes: details

The following classes were open earlier and are now decided; the notes record how.

* **Superelliptic curves `yⁿ = p(x)`** (`gcd(n, deg p) = 1`): the residue-free class
  `∫ B(x) p(x)^{a/n} dx` (`n ∤ a`) is decided (`super_decides_pow`), and the geometric theory (local
  expansions at all places, degree theorem, integral closure, Abel's direction, residue-free ⇒
  exact) is in place, over any perfect constant field in which `n` is invertible (so also over
  `𝔽̄_p`). Proved for the torsion theory of superelliptic Jacobians (standard axioms): a computable
  principality test `supPrincipalC` (sound and complete); the kernel of reduction has no
  prime-to-`p` torsion (`Sup.kernel_no_torsion_N`, any DVR, under a non-speciality hypothesis on
  the base points); **`Sup.torsion_descends_N`** (Henselian DVR: a class of order prime to `p`
  that is trivial modulo `ϖ` is trivial), via the exact divisor of the reduced auxiliary function
  (`structure_k`, `norm_structure`), Hensel lifting of the residual zeros and a disc-uniqueness
  argument (`residual_zeros_N`, `disc_unique_N`), and the `ℓ`-th power step. Also proved: the
  two-prime criterion `torsion_iff_two_primes_N`, finiteness of `Pic⁰` over finite fields
  (`exists_principalMulN`), checked good-prime certificates (`supBaseCheck_spec`) and a torsion
  decision for points over `ℚ` (`torsionDecideN_iff`). **The logarithmic part is decided**
  (`Algebraic/SupLog*.lean`, standard axioms): `Sup.superLogDecide f n ζ tors B B₁ a b G`
  handles `∫ (B(x,y) + B₁(x,y)/p(x) + ∑ᵢ Gᵢ(x,y)/(x − aᵢ)) dx` (data in a field with a computable
  `ℚ`-basis containing a primitive `n`-th root `ζ`, `B₁` without `y⁰` term, `p(aᵢ) ≠ 0`).
  It splits the residues `Gᵢ(aᵢ, ζᵏbᵢ)` along the basis, asks a torsion oracle about each
  component, builds the logarithms from `supPrincipalC` witnesses, and decides the remainder with
  a linear exactness test (`exactTest`). `Sup.superLogDecide_spec`: given any oracle satisfying
  `TorsSpecN`, every answer is correct (`some true` ⟺ elementary). The key theorems are
  `log_exact` (a residue-free remainder of a Liouville form is `(elemW V)′` with bounded
  support), `abel_component`, `exact_complete` and `superLog_sound`. With the search oracle
  `torsSearch` (positive answers only, `torsSearch_spec`), examples are run by the kernel
  (`Algebraic/SupLogExample.lean`): on `y² = x³ + 1`, `∫ √(x³+1)/x dx` is elementary (log part of
  order 3), `∫ (√(x³+1)/x − (3/2) x/√(x³+1)) dx` and `∫ dx/√(x³+1)` are not. **A torsion oracle
  with non-torsion proofs** (`Algebraic/SupRed*.lean`): `torsOracle redAt ps bound f n` works over any
  field with computable reductions (`RedFns`: `ℚ` via `ratFns`, number fields `ℚ[θ]/(M)` via
  `nfRedAt`, with the embedding into `ℚ_p` from Hensel's lemma). It searches the candidate primes for
  roots of unity, base points and a non-speciality certificate (linear algebra mod `p`), checks them
  (`supCheckR`, `supCheckR_spec`), computes the orders `m_p, m_q` and tests principality at
  `gcd(m_p p^k, m_q q^k)` (`torsDecideR_spec`). `torsOracle_spec`: it satisfies `TorsSpecN`.
  Kernel-checked examples: `∫ (1/2 + y/10)/(x − 3) dx` on `y² = x³ − 2` is not elementary
  (`(3, 5)` has infinite order; `SupRedExample`); over `ℚ(ζ₃)`, `∫ ∛(x²+1)/x dx` is elementary and
  `∫ ∛(x²+1) dx` is not (`SupRedNFExample`). **General integrands** (`Algebraic/SupFront*.lean`,
  `HermiteSup*.lean`): `superFront f n ζ tors A D a b` takes `∫ ∑_{j<n} (Aⱼ/D) yʲ dx`. The rational
  part is always elementary. For each `j ≥ 1`, Hermite reduction for `L_{j/n}(U) = U′f + (j/n)Uf′`
  is solved by linear algebra (`hermiteS_solve_ne_none`: always solvable, through a general
  existence theorem `hermite_existsS`). Partial fractions are taken at the given roots `aᵢ` of the
  non-branch part of `D`, then `superLogDecide` runs. `superFront_spec`: every answer is correct;
  `superFront_ne_none`: it always answers on valid splitting data when the oracle answers.
  **Good primes** (`Algebraic/SupRedG*.lean`, `SupFrontEvent.lean`): with global base points
  `(xᵢ, yᵢ)` and a global non-speciality certificate over `K = NF M` (`globalCert`), all large
  primes at which `M` has a simple root (Schur's theorem) are good (`goodPrime_eventually`, via the
  reduction homomorphism `psiRed` on the `p`-integral subring). So the oracle eventually answers
  (`torsOracleG_eventually`), and `superFront_eventually` shows the front end answers for every
  large bound. **Rational input, end to end** (`Algebraic/SupDecideQ.lean`):
  `superDecideQ f n A D B fuel` (`f, Aⱼ, D ∈ ℚ[x]`) builds the number field itself: it splits
  `Xⁿ − 1` and the non-branch part of `D`, and adjoins `n`-th roots of `f` at those roots
  (`splitLoop`, `nthLoop`). It then runs `superDecideM M` over the field `ℚ[θ]/(M)`, which finds and
  checks the data and runs `superFront` with the search oracle.
  `superDecideQ_spec` and `superDecideM_spec` (the latter for any irreducible `M`): every answer
  is correct (constants algebraically closed). Kernel-checked (`SupDecideQExample`): on
  `y³ = x² + 1`, `∫ ∛(x²+1)/x dx` is elementary and `∫ ∛(x²+1) dx` is not, with `ℚ(ζ₃)` constructed
  automatically. The kernel evaluates this in stages (`superDecideQ_eq`): first the field `M` is
  computed and checked to be a literal, then `superDecideM` runs over that literal. Inside a single
  `match`, the unevaluated `M` would be recomputed and exhaust memory. Kronecker's search now
  discards candidates cheaply, by integrality (`intC`) and by divisibility of values at extra
  points (`valTest`), before the expensive trial division over `ℚ`. Both filters are proved
  harmless (`intC_of_toPoly_eq`, `valTest_of_toPoly_eq`), so `irredQ_sound` and `factorQ_spec` are
  unchanged. **`n ∣ deg f`** (`Algebraic/SupMobius.lean`, `SupDecideAll.lean`): infinity is then
  unramified (`n` places). `superFrontMob` moves a branch point `e` to infinity: with `t = 1/(x − e)`
  and `w = y t^{deg f / n}`, we get `wⁿ = P(t)` with `deg P = deg f − 1`, which is coprime to `n`.
  The derivation is rescaled by `−1/t²` (`hasElementaryIntegral_rescale_iff`), the integrand is
  rewritten over a common denominator (`mobData`), and `superFront` runs on the new curve
  (`superFrontMob_spec`). `superDecideMobQ` builds the field (it also contains the roots of `f` and
  an `n`-th root of its leading coefficient). `superDecideAll` dispatches on
  `gcd(n, deg f) = 1` versus `n ∣ deg f`; `superDecideAll_spec` shows every answer is correct. For
  prime `n` this covers every squarefree `f`. Kernel-checked (`SupDecideAllExample`): on the Fermat
  cubic `y³ = x³ + 1`, `∫ x²/y² dx` is elementary and `∫ ∛(x³+1) dx` is not. Completeness
  (all done; see `superDecideFull_complete` below):
  * the field loops always succeed: done (`Algebraic/SupFieldComplete.lean`).
    `nthLoop_spec` and `buildField_spec` show the loops succeed once `fuel > max(n, deg S)`.
    `superDecideM_ne_none` and `superDecideQ_ne_none_of` then show that `superDecideQ` answers
    whenever the torsion oracle answers on its queries (`TorsAnswers`). The supporting lemmas
    are: a primitive root exists among `n` distinct roots of unity (`exists_primRoot_of_roots`),
    and the non-branch part over `K` splits as `lc·∏(X − aᵢ)` over the roots found
    (`nbPart_split`, proved through the algebraic closure). So the torsion oracle's answering is
    the only missing hypothesis for `superDecideQ` to always answer. The same holds for the other
    two cases (`Algebraic/SupMobComplete.lean`, `SupSupComplete.lean`):
    * `superFrontMob_ne_none` works over any field containing the non-branch roots of `D`, `n`-th
      roots of `f` there and an `n`-th root of `lc f`. It rests on the facts that `P` is squarefree
      with `P(0) = lc f` and `P(β) = βᵈ f(e + 1/β)`, and on locating every new non-branch point
      through the algebraic closure.
    * `buildFieldMob_spec` proves the field construction for this case succeeds.
    * `coverC_spec` shows the chosen `c` is not a root of `f`, and `squarefree_comp_shiftPow` shows
      `f(c + Xᵏ)` is then squarefree.
    * `superDecideSup_eventually`: for every squarefree `f ∈ ℚ[x]` of positive degree, every
      `n ≥ 1` and every `D ≠ 0`, `superDecideSup` answers for all large `fuel` provided the
      torsion oracle answers (`TorsAnswers`).
  * **The oracle hypothesis is discharged** (`SupNonSpecial`, `SupGlobalCert`, `SupCertSearch`,
    `SupOracleFB`, `SupCands`, `SupDecideC`, `SupDecideFull`). **Global non-special base points
    exist** (`exists_nonspecial`, `exists_lam`, `exists_cert_lists`). The certificate identity is
    equivalent to invertibility of the matrix `(xᵢˢ yᵢ⁻ʲ)` of the holomorphic monomials
    `xˢ dx/yʲ`, `n(s+1) < dj`; there are exactly `g` of them (`exists_hol`, pairing `j ↔ n − j`).
    The proof uses:
    * duality in the space of weighted monomials (`mem_span_of_iInf_ker_le_ker`);
    * discrete Fourier inversion on each fibre (`dft_const`, `dft_zero`);
    * the Lagrange identity `∑ p(xᵢ)/∏(xᵢ − x_l) = 0` (`Lagrange.coeff_eq_sum`);
    * an inductive choice of points: a non-zero combination cannot vanish on all `n` conjugates
      over a good `x` (`exists_good_point`).

    `solveLamF` (sound and complete linear algebra) and `certSearch` (all ordered choices among
    candidate points) find a certificate. `torsOracleFB` runs the search oracle and then the
    global-certificate oracle; it is sound (`torsOracleFB_spec`) and answers every valid query for
    large bounds (`torsOracleFB_eventually`). `buildFieldAll` adds `n`-th roots of `f` at
    `candQ` rational candidates. `superDecideMobMC`, `superDecideMobQC` and `superDecideCoverC` use
    this oracle; their completeness goes through `superFrontMob_data`, whose transformed data do
    not depend on the oracle, so the finitely many queries get a common bound.
  * **`superDecideFull`** (`n ≤ 1`: rational integrand, always elementary by
    `hasElementaryIntegral_rational_in`; otherwise fast `superDecideSup`, then complete
    `superDecideCoverC`):
    * `superDecideFull_spec`: every answer is correct;
    * **`superDecideFull_complete`: for every squarefree `f ∈ ℚ[x]` of positive degree, every `n`
      and every `D ≠ 0`, there is `B₀` such that it answers for every `B ≥ B₀` and every fuel.**

    So for superelliptic integrands with rational data the procedure is a sound and complete
    decision procedure, with no remaining hypothesis. (The complete fallback is exponential and
    builds large fields, so it is not practical for kernel evaluation; the kernel-checked
    examples are answered by the fast path.)
  * general algebraic curves beyond the superelliptic ones — see *General algebraic curves*
    below (sound decision with verified certificates; the non-torsion theory is proved, its
    certificate layer is still missing).

  **`1 < gcd(n, deg f) < n`, through a cover** (`Elementary/FiniteBase.lean`,
  `Algebraic/SupCover.lean`). Elementary integrability is invariant under finite extensions of the
  base: `hasElementaryIntegral_finite_iff` says `h ∈ E` has an elementary integral over a finite
  differential extension `E'` iff it has one over `E`. For `→`, the elementary extension `L` of `E`
  is enlarged to a splitting field over which `E'` embeds, compatibly with derivations
  (`algHom_deriv'`), and the tower is changed to base `E'` (`IsElementaryTower.baseChange`). With
  `k = n / gcd(n, deg f)` and `c ∈ ℚ`, the procedure adjoins `s` with `sᵏ = x − c`, taking a root of
  an irreducible factor of `Sᵏ − (x − c)` in `AdjoinRoot` with Mathlib's derivation. Over `Kc(s)`
  the curve is `yⁿ = f(c + sᵏ)`, whose degree is divisible by `n`. Rescaling the derivation by
  `k sᵏ⁻¹` makes `s′ = 1`, so `superDecideCover` runs `superDecideMobQ` on the substituted rational
  data (`superDecideMobQ_cover_spec`). `superDecideSup` dispatches all three cases;
  `superDecideSup_spec` shows every answer is correct for every squarefree `f` and every `n`.
  Kernel-checked (`SupCoverExample`): on `y⁴ = x² − 1`, where `gcd(4, 2) = 2`, the procedure uses
  the cover `s² = x`, on which the curve is `y⁴ = s⁴ − 1` of genus 3 over `ℚ(i)`. There,
  `∫ x y/(2x² − 2) dx` is elementary and `∫ ∜(x² − 1) dx` is not. With the default bound `B = 30`
  the torsion search found no certificate on that genus-3 cover; `B = 60` was used. An integrand
  with a genuinely logarithmic part (`∫ dx/√(x² − 1)`) exceeded a 16G kernel budget at `B = 60`.
  This is a practical limit of the kernel search, not of soundness.

  **Faster Kronecker search in the kernel.** Before any rational interpolation or division,
  candidate tuples of values pass an integer filter (`zFilter`). It computes `W·g` from the
  precomputed integer basis `basisZ`, and requires `W` to divide every coefficient and `g(b)` to
  divide `F(b)` at a few points. `zFilter_of` proves that every integral factor passes, so
  `irredQ_sound`, `noFactor_complete` and `factorQ_spec` hold unchanged.
* **Genus ≥ 1 (hyperelliptic) — now decided for every `∫ A dx/(D √q)` with `q ∈ ℚ[x]`
  squarefree of degree ≥ 3, odd or even** (`hypDecideOdd_decides`, `hypDecideEvenQ_decides`,
  below). Curves over a number field are decided by `hypDecideNFC` / `hypDecideEvenK` once the
  field contains the splitting data. Still open: building that field automatically for a curve
  with irrational coefficients (splitting polynomials over a number field). The elementary direction was already
  automated (`hypDecideAllLog`). The torsion theory
  for hyperelliptic Jacobians `y² = f(x)`, `deg f = 2g+1`, is now proved in `Jacobian/` (standard
  axioms only), without formal groups: divisors in "ψ-form" (`ψ = a + b y` vanishing along branch
  jets, `PrincipalMul`); the kernel of reduction has no prime-to-`p` torsion
  (`kernel_no_torsion`, any DVR); `torsion_descends`, `principal_of_reduction`;
  `torsion_iff_two_primes` (`D` torsion ⟺ `(m_p m_q) D` principal); `not_torsion_of_orders`
  (exact orders at two primes with `m_p pᶜ ≠ m_q qᵈ` ⇒ not torsion); a computable principality
  test `principalC` (sound, complete over field extensions) and kernel-checkable certificates
  `principalCert`; Abel's direction in any genus `hyp_principal_of_elementary` (elementary ⇒ the
  residue divisor is torsion). Example (`Jacobian/Genus2Example.lean`,
  `genus2_not_elementary`): `∫ dx / (x √(x⁵ − 2x² − 3x + 1))` is **not elementary** (orders 7
  mod 7 and 13 mod 11, certificates checked by `decide +kernel`). **Semi-automated, any genus**
  (`Jacobian/CertCheck.lean`, `Jacobian/NonElemCheck.lean`): for `f ∈ ℤ[x]` and simple poles at
  integral points `(aᵢ, bᵢ)` with integer residues `zᵢ`, the Boolean `nonElemCheck` (local
  checks at two primes: `E₀` modulo `p` lifted by Hensel, a `principalCert` for `m Γ̄`,
  `principalC … = none` for `(m/r) Γ̄`, an incompatibility witness `r^k`) implies
  `¬ HasElementaryIntegral ((B(x) + ∑ zᵢ bᵢ/(x − aᵢ)) / y)` for **any** `B`
  (`not_elementary_of_check`). `findCert` searches primes and orders (untrusted; its output is
  re-checked by the kernel). Still missing: rational/irrational residues and poles in general
  position (number fields), the combination with Hermite reduction and the elementary side into
  one procedure, and **completeness**. Finiteness of `Pic⁰` over finite fields is now proved
  (`Jacobian/PicFinite.lean`, `exists_principalMul`: over a finite field of odd
  characteristic every `Γ` on non-branch points has a principal positive multiple). The proof
  identifies the ring of integers of `k(x)[y]/(y² − f)` with `k[x] ⊕ k[x] y` (`f`
  squarefree), uses Mathlib's finite class group of function fields, and shows `I·σ(I) = (w)` for
  the ideal `I` of `Γ` (Chinese remainders for the branch jets). **Torsion is now decided
  unconditionally** (`Jacobian/TorsionDecide.lean`, `GoodPrimes.lean`, `TorsionDecideU.lean`):
  `torsionDecide` computes the orders modulo two good primes by `Nat.find` over `principalC`
  (terminating by `exists_principalMul`), then runs one `principalC` test over `ℚ`
  (`torsionDecide_iff`). `exists_goodPrime` produces good primes: primes `p ≡ 1 (mod 8∏|f(aᵢ)|)`
  make every `f(aᵢ)` a square by quadratic reciprocity, and `f` stays squarefree mod `p` by a
  Bézout identity over `ℤ`. `findE0_good` shows that the search for `E₀` is complete, and
  `torsionDecideU_iff` gives, for every squarefree `f ∈ ℤ[x]` of degree `2g + 1` and every
  divisor on integral non-branch points, a total procedure deciding whether it is torsion.
  **Complete decision on the integrand level** (`Jacobian/HypDecideG.lean`, `hypDecideG_iff`):
  for `y² = f(x)`, `f ∈ ℤ[x]` squarefree of degree `2g + 1`, `hypDecideG` decides elementarity
  of every `∫ (B(x) + ∑ (zᵢ/D) bᵢ/(x − aᵢ)) dx / y` with `B ∈ ℚ[x]` and poles at integral
  non-branch points `(aᵢ, bᵢ)`. If the residue divisor is not torsion, the answer is "not
  elementary". Otherwise `principalC` computes `A + B y` with divisor `n Γ`, and
  `1/(nD)·log(A + B y)` is split off. This step is checked by `certCheck`, which always succeeds
  by `certCheck_ok_odd`, the elliptic `certCheck_ok_gen` generalised to any odd degree. The
  residue-free remainder is then decided by `hyp_decides`. **Hermite front end**
  (`Jacobian/HypDecideGenQ.lean`, `hypDecideGenQ_spec`): arbitrary `∫ A dx/(D √f)` with
  `A, D ∈ ℚ[x]`. The Hermite reduction `A/(Dy) = (W/D·y)′ + T/(S y)` is linear algebra, the
  partial fractions of `T/S` are re-checked, and the result goes to `hypDecideR`. Every answer
  is proved correct. The procedure answers whenever the non-branch poles are **rational** points
  of the curve; completeness of this front end is not yet proved. `hypDecideR` (rational points)
  decides torsion by rescaling `(x, y) ↦ (d²x, d^{2g+1}y)` to an integral model
  (`Jacobian/Scale.lean`, `principalMul_scale_iff`, `TorsionDecideR.lean`). `torsionDecide`
  first tries the cheap incompatible-orders test (`findWitness`, `not_torsion_of_orders`).
  **Decision theorem** (`Jacobian/HypDecideGen.lean`, `hypDecideGen_decides`): for
  `∫ A dx/(D √f)` with `D` split over `ℚ` and every root of `D` off the branch points under a
  rational point, `hypDecideGen` always answers, and the answer is proved correct. It reuses the
  elliptic Hermite/partial-fraction solver `ellHermite`, whose completeness proof is
  degree-generic, and `hypDecideR_ne_none` / `torsionDecideR_ne_none`: the rescaled points are
  integral (`ScaleInt.lean`), and rescaling keeps `f` squarefree. Speed: orders modulo `p` are
  proposed by Cantor's algorithm (`Jacobian/Cantor.lean`, untrusted) and verified by
  `principalC` (`orderOk` + `exact_order`), with `Nat.find` as fallback; residue numerators are
  divided by their gcd before the torsion test. Examples (`HypDecideGenQExample.lean`, `#eval`,
  about 2 s each): `∫ dx/(x√(x⁵+1))` elementary; `∫ dx/(x√(x⁵−2x²−3x+1))` and
  `∫ dx/((4x−9)√(x⁵−2x²−2x−2))` (pole at the rational point `(9/4, 205/32)`) not elementary.
  **Irrational poles and residues** (`Jacobian/HypDecideK.lean`, `NFEmbed.lean`,
  `CertCheckK.lean`, `TorsionDecideK.lean`, `NFSplitG.lean`, `HypDecideNF.lean`):
  - `hypDecideK` handles poles and residues in a number field with a ℚ-basis (`QCoords`). It
    splits the residues along the basis, as `ellDecideK` does, and then runs one torsion test per
    coordinate.
  - The torsion tests are answered by the oracle `torsNF`. For `K = NF M` it reduces at two good
    primes (`embedZ`, `exists_lift_NF`, `baseCheckK_spec`, `torsFrom_spec`), and `torsNF_spec`
    proves its answers correct.
  - `hypDecideQ` runs the whole chain for arbitrary `∫ A dx/(D√f)` over `ℚ`: Hermite reduction,
    then `splitFieldG` (the elliptic splitting field generalised to any curve), then `rootsIn`,
    `sqrtNF` and `hypDecideADK`.
  - `hypDecideQ_spec`: every answer is correct.
  - **Completeness** (`Jacobian/GoodPrimesK.lean`, `TorsNFComplete.lean`,
    `HypDecideNFComplete.lean`, `HypDecideQComplete.lean`). `exists_goodK` produces good primes
    above any bound (Schur's theorem for `M`, Hensel, reductions `redL` of all relevant
    elements, `findE0K_good`). At a good prime the reduced divisor has finite order
    (`exists_principalMul`), so `ordZ` succeeds, and `torsNF_eventually` follows. For this,
    `hypDecideQ` also splits `S ∏ (X − aᵢ)` for `g` integers `aᵢ` (`baseAs`, `baseS`), so that
    the field contains base points `(aᵢ, √f(aᵢ))`. `hypDecideNF_eventually` and
    `hypDecideQ_eventually` then show that the procedure answers for all large bounds `B`.
  - **Decision theorem** `hypDecideQ_decides`: for `f ∈ ℤ[x]` squarefree of degree `2g + 1`
    (leading coefficient last) and any `A, D ∈ ℚ[x]`, `D ≠ 0`, there is `B₀` such that for all
    `B ≥ B₀` the procedure `hypDecideQ f g A D B` returns `some ans`, with `ans = true` iff
    `∫ A dx/(D y)` is elementary (standard axioms only).
  - **Rational coefficients and even degree** (`Jacobian/HypDecideRat.lean`,
    `HypDecideEven.lean`). `hypDecideOdd` takes `q ∈ ℚ[x]` of degree `2g + 1` and passes the
    integral model `Y = m y`, `Y² = m² q` (`sqModel`, `m` a common denominator) to
    `hypDecideQ`. `hypDecideEven` takes `q` of degree `2g + 2` with `q(e) = 0` and
    substitutes `t = 1/(x − e)`, `Y = y t^{g+1}`. This gives `Y² = P(t)` with `deg P = 2g + 1`,
    where `P` is the reversal of `q(x + e)/x`; squarefreeness is kept by `squarefree_reflect`
    and `squarefree_comp_add_C`. Rescaling the derivation by `−1/t²` makes `t′ = 1`, as for
    quartics in genus 1.
    - `hypDecideOdd_decides` and `hypDecideEven_decides`: for all large bounds the procedure
      answers, and the answer is correct.
  - **Curves over a number field** (`Jacobian/HypKc.lean`, `HypDecideKF.lean`,
    `CertCheckKF.lean`, `TorsionDecideKF.lean`, `GoodPrimesKF.lean`, `TorsNFFComplete.lean`,
    `HermiteK.lean`, `HypDecideNFC.lean`, `HypDecideNFCComplete.lean`). The same pipeline
    handles `y² = f(x)` with `f ∈ K[x]`, `K = NF M`, and `A, D ∈ K[x]`:
    - the theory (Abel's direction, the residue-free remainder) for a curve over any
      `F ⊆ Kc` (`hyp_principal_of_elementaryKc`, `hyp_no_elemKc`, `hyp_decidesKc`);
    - `hypDecideKF`, the torsion oracle `torsNFF`: the curve is reduced coefficientwise, and
      `baseCheckKF` lifts it to `F ∈ ℤ_p[x]`;
    - good primes above any bound (`exists_goodKF`): Bézout and `bᵢ² = f(aᵢ)` are lifted to
      `ℤ_p` and reduced;
    - Hermite reduction over `K` (`hermite_solve_ne_noneK`, through the algebraic closure
      of `K`).
    `hypDecideNFC_spec`: every answer is correct, for any embedding `K → Kc`.
    `hypDecideNFC_eventually`: the procedure answers for all large bounds, provided the
    non-branch part of `D` splits over `K` with `f` a non-zero square at its roots, and `K`
    contains `g` base points (with abscissae in `K`).
  - **Even degree without a rational root** (`Jacobian/NFTower.lean`, `HypDecideEvenK.lean`,
    `HypDecideEvenKComplete.lean`, `HypDecideEvenQ.lean`). `hypDecideEvenQ` works as follows:
    - `towerEven` builds a number field `K` by chaining `splitLoop` and `sqLoopG`. The loops
      extend their input field (`splitLoop_emb`, `sqLoopG_emb`), and roots and square roots
      transport along the embeddings (`roots_map`, `sqFacts_map`).
    - In `K`: the non-branch part of `D` splits, `q` is a non-zero square at its roots and at
      `g` integer base abscissae, `lc(q)` is a square, and `q` splits.
    - A root `e ∈ K` of `q` gives `t = 1/(x − e)`, `Y = y t^{g+1}` over `K` (`evenDataK`), and
      `hypDecideNFC` decides the resulting odd-degree integral.
    - In the `t`-model the poles are `t = 0` and `1/(α − e)`, where `P(0) = lc(q)` and
      `P(1/(α − e)) = (α − e)^{-(2g+2)} q(α)`. The non-branch part splits because its roots in
      `K̄` lie in `K`.
    `hypDecideEvenQ_decides`: for `q ∈ ℚ[x]` squarefree of degree `2g + 2` and any `A`, `D ≠ 0`,
    the procedure answers for all large bounds, and correctly.
  The number-field pipeline runs in the kernel, and `torsFrom` first tests `lcm(m_p, m_q)`.
  Example (`Jacobian/HypDecideNFExample.lean`): `x5_elementary`, a theorem that
  `∫ dx/(x√(x⁵+1))` is elementary, with the answer `hypDecideNF … = some true` checked by
  `decide +kernel` (4 s). The splitting-field search (`splitFieldG`) is too slow for the kernel,
  so kernel-checked examples supply the field. The example `∫ dx/((x²−2)√(x⁵+x³+11))` over
  `ℚ(√2)` exhausts 8 GB in the kernel. So the decision is proved, but kernel evaluation over
  non-trivial number fields is currently impractical.
* **Elliptic curves with irrational residues — now closed for curves over `ℚ`**: with
  `ellDecideGenQ` (below) every `∫ A(x) dx / (D(x) √(x³+ax²+bx+c))`, `A, D ∈ ℚ[x]`, is decided
  (sound and complete). What remains open in genus 1 is only curves whose coefficients are
  themselves irrational. The history of this item: `Elliptic/DV/` generalises the Nagell–Lutz filtration argument to any
  characteristic-zero field with a discrete valuation normalised by `v(p) = 1`. It proves the
  kernel of reduction is torsion-free (`EllDV.torsion_integral_y`) and, over `ℚ_p` (`p` odd,
  good reduction), the kernel lemma (`kernel_big`) and the **torsion bound**
  `addOrderOf P ≤ #(Option Ẽ(𝔽_p))` (`torsion_order_le`). A number field `ℚ(α)` embeds in
  `ℚ_p` whenever `α`'s minimal polynomial has a simple root mod `p`. This is now proved
  (`Elliptic/DV/Embed.lean`): `hensel_root`, `torsion_order_le_field` (any field with a
  `ℚ`-embedding into `ℚ_p`, via Mathlib's `Point.map`), and `torsion_order_le_adjoin` for
  `ℚ[x]/(f)`. Good reduction is a finite check mod `p` (`goodRedMod`, `goodRed_of_mod`).
  **Verified torsion test over number fields** (`Elliptic/DV/Chain.lean`). Point arithmetic in
  `ℚ[x]/(f)` (`addPt`, `mulPt`; inverses by the extended Euclidean algorithm) is proved to agree
  with Mathlib's group law (`addPt_spec`, `mulPt_spec`). `torsionTestK_spec`: with `N` at least
  the reduction bound, `torsionTestK` is `true` **iff** the point has finite order. **Abel's
  direction with arbitrary residues** (`Algebraic/EllFunctional.lean`, `ell_torsion_functional`):
  for points `Pᵢ` and residues `rᵢ` in the constant field (not necessarily rational), if the
  integral is elementary then `Σ zᵢ Pᵢ` has finite order for **every** `ℚ`-linear functional `Λ`
  with `Λ(rᵢ) = zᵢ/D`. The proof uses `ell_glue`, Abel's theorem for each logarithm, and an
  extension of `Λ` to the constants of the elementary extension (`LinearMap.exists_extend`).
  Together with `torsionTestK` this gives computable "not elementary" certificates for irrational
  residues whenever the residue field is available, e.g. a quadratic orbit with `r = u + v√d`:
  test `u(P + σP)` and `v(P − σP)`. `not_elem_of_nontorsion` packages this: a non-torsion point
  over any field `K` embedded in the constants refutes elementarity. **Example**
  (`Algebraic/EllIrrationalExample.lean`): `∫ (4x+4) dx/((x²−2)√(x³+x²+1))`, with **irrational**
  residues `±√2` at `P = (√2, 1+√2)` and `σP`, is proved **not elementary** (constants containing
  `√2`). The certificate is that `P − σP = (−1/2, −¾√2)` has infinite order in `E(ℚ(√2))`, from
  `torsionTestK` at `p = 7` in the kernel. **The elementary direction over number fields**
  (`Algebraic/HypLogField.lean`). Log certificates `A/(Dy) = (W/V·y)′ + Σ κₖ uₖ′/uₖ` may have
  coefficients in any computable field `F` embedded in the constants, for example Mathlib's
  `QuadraticAlgebra ℚ d 0 = ℚ(√d)` (`logCheckF`, sound by `logCheckF_sound`). The Riemann–Roch
  search runs over `F` (`logCertF`). **Example** (`Algebraic/EllIrrationalElemExample.lean`):
  on `y² = x³+2x²−2x`, `P = (√2, 2)` and `σP` satisfy `2(P − σP) = 0`, and
  `∫ (2x²+4) dx/((x²−2)√(x³+2x²−2x)) = (√2/2)·log((a+by)/(x²−2)²)` with `a, b ∈ ℚ(√2)[x]`. The
  certificate is checked by the kernel, so the integral is proved **elementary**. The torsion
  conditions alone are not enough: for `8/((x²−2)y)` the same log part leaves the holomorphic
  remainder `−2dx/y`. Certificates with a remainder (`logCheckFB`, `Algebraic/EllQuadOrbit.lean`)
  give both answers. If the remainder is zero the integral is elementary (`elem_of_logCheckFB`).
  If it is a non-zero rational polynomial of degree `≤ deg p − 2`, the integral is **not
  elementary** (`not_elem_of_logCheckFB`: subtract the logarithms, then `hyp_no_elem`). The
  example `ex_irrational_remainder_not_elementary` proves `∫ 8dx/((x²−2)√(x³+2x²−2x))` is not
  elementary. Point arithmetic and the torsion
  test also run directly over any computable field embedded in `ℚ_p`, such as `ℚ(√d)`
  (`Elliptic/DV/ChainF.lean`: `addPtF_spec`, `mulPtF_spec`, `torsionTestF_spec`). So both
  directions now use one representation of the residue field. **Decision procedure for one
  quadratic orbit** (`Algebraic/EllQuadDecide.lean`, `quadOrbitDecide`). Input: `y² = x³+ax²+bx+c`
  and `A/(Dy)`, where `D` is a monic quadratic with a root `α ∈ ℚ(√d) \ ℚ` over which `p` takes a
  non-zero square value. It also needs a good odd prime `p` with `√d ∈ 𝔽_p`. The procedure
  computes the residue `r = u + v√d` (`orbitData`, with complete square-root searches in `ℚ` and
  `ℚ(√d)`). It then runs `torsionTestF` on `P + σP` (if `u ≠ 0`) and on `P − σP` (if `v ≠ 0`). A
  point of infinite order gives **not elementary** (`not_elem_of_nontorsion` with `Λ = re`,
  resp. `im`). Otherwise, with `n` the order of the point, a linear solve over `ℚ(√d)` finds
  `A + B y` with the right divisor, and the kernel check removes that logarithmic part
  (`certPart_spec`, via `ell_log_decompK` for constant coefficients). The polynomial remainder is
  reduced by `hypRed` over `ℚ(√d)`. The integral is elementary **iff** the holomorphic remainder
  vanishes (`hyp_decidesF`, via `hyp_no_elemK`: `B₀ dx/y` with arbitrary constant coefficients
  has no elementary integral). Both directions are proved:
  * `quadOrbitDecide_spec`: every answer is correct;
  * `quadOrbitDecide_ne_none` and `orbitData_ne_none`: on the class the procedure always
    answers. The certificate is found because the ideal of the divisor is principal in the
    Dedekind coordinate ring over `ℚ(√d)` (`EllAlgo.exists_localW`; `EllSolve`, `EllCertValid`,
    `EllExist` and `HypRed` are now stated over any field of characteristic zero);
  * `quadOrbitDecide_decides` combines the two.

  **Examples** (`Algebraic/EllQuadDecideExample.lean`, where the kernel runs the procedure):
  `(4x+4)/((x²−2)√(x³+x²+1))`, `(2x²+4)/((x²−2)√(x³+2x²−2x))` and `8/((x²−2)√(x³+2x²−2x))` are
  decided as non-elementary, elementary and non-elementary.

  **Any number of conjugate pairs and rational points at once** (`Algebraic/EllDecideF.lean`,
  `ellDecideF`). Input: `∫ (B(x) + Σ rᵢ βᵢ/(x − αᵢ)) dx / y` with poles at points `(αᵢ, βᵢ)` of
  `E(ℚ(√d))` (distinct `αᵢ`, `βᵢ ≠ 0`), residues `rᵢ ∈ ℚ(√d)` and `B ∈ ℚ(√d)[x]`. The procedure
  splits the residues along `1, √d`. It tests `Σ (L₁ re rᵢ) Pᵢ` and `Σ (L₂ im rᵢ) Pᵢ` for torsion
  over `ℚ(√d)`; if either has infinite order the answer is **not elementary**
  (`not_elem_of_nontorsionK`, now with constant-coefficient `B`). Otherwise it removes both
  logarithmic parts by certificates (`partCert`) and reduces the remainder. Proved:
  `ellDecideF_spec` (every answer is correct), `ellDecideF_ne_none` (valid data is always
  decided) and `ellDecideF_decides`. A kernel-run example mixes a conjugate pair with the rational
  point `(1, 1)` (`auto_mixed_not_elementary`).

  **Front end for `∫ A dx / (D √p)`** (`Algebraic/EllDecideAD.lean`, `ellDecideAD`). It factors `D`
  over `ℚ` (Kronecker, `Kron.factorQ`, complete). It takes the roots of the linear and quadratic
  factors in `ℚ(√d)` (`rootsFac`), the ordinates by `sqrtF` and the residues
  `A(α)/(D′(α)β)`, and then runs `ellDecideF`. The partial-fraction identity comes from Lagrange
  interpolation (`partial_frac`, via Mathlib's `Lagrange.eval_interpolate_not_at_node`).
  `ellDecideAD_spec`: every answer is correct. `ellDecideAD_ne_none`/`ellDecideAD_decides`: it always
  answers when `D` is squarefree and splits over `ℚ(√d)`, and `p` takes non-zero square values at
  the roots of `D`. Along the way: an irreducible rational polynomial with a root in `ℚ(√d)` has
  degree `≤ 2` (`natDegree_le_two_of_root`); each factor of a split polynomial has one of the roots
  (`exists_root_of_dvd`); a squarefree polynomial has distinct roots (`nodup_of_squarefree`).
  Example: `∫ dx / ((x²−2)(x−1)√(x³+2x²−2x))` is proved not elementary by the kernel
  (`auto_AD_not_elementary`).

  **Any number field of constants** (`Algebraic/EllDecideK.lean`, `Algebraic/NumField.lean`).
  `ellDecideK` is `ellDecideF` for any field `K` of characteristic zero with a computable ℚ-basis
  (`QCoords K`). Residues are split along the basis, with one torsion test and one certificate per
  coordinate. `ellDecideK_spec` (every answer is correct) and `ellDecideK_ne_none` (valid data is
  always decided) are proved. `NF f` is a **computable number field** `ℚ[x]/(f)` for any
  irreducible `f`. Elements are reduced coefficient lists, and the field structure is transported
  from Mathlib's `AdjoinRoot` along an injective map (`Function.Injective.field`). `NF f` has the
  power basis as its `QCoords`, and `exists_embedNF` embeds it into `ℚ_p` by Hensel from a simple
  root mod `p`. `ℚ(√d)` is also an instance. Example (`Algebraic/NumFieldExample.lean`, over the
  **non-normal cubic field** `ℚ(∛12)`, curve `y² = x³ − 3`, point `(∛12, 3)` of order 3, all
  run in the kernel): `∫ 3 dx/((x − ∛12)y)` is not elementary, and
  `∫ (∛144/6 + 3/(x − ∛12)) dx/y` is elementary.

  **Rational integrands with residue fields of any degree, from checked splitting data**
  (`Algebraic/EllDecideADK.lean`, `ellDecideADK`). Given rational `A, D` and pairs `(αᵢ, βᵢ)` in a
  number field `K`, it checks by computation that `D = lc ∏ (X − αᵢ)` over `K` (`splitCheck`) and
  that `βᵢ² = p(αᵢ)`. It then computes the residues and runs `ellDecideK`. `ellDecideADK_spec`:
  every answer is correct. `ellDecideADK_ne_none`: correct splitting data is always decided.
  Example: over the cyclic cubic field `ℚ(θ)`, `θ³ − 3θ + 1 = 0`,
  `∫ dx / ((x³ − 3x + 1)√(x³ + x² − x + 2))` is proved not elementary (`cyclic_not_elementary`).

  **Root finding in number fields (Trager's norm method)** (`Computable/ResultantC.lean`,
  `Algebraic/NFNorm.lean`, `Algebraic/NFRoots.lean`):
  * `resC` is a computable Euclidean resultant, proved equal to Mathlib's Sylvester resultant
    (`resC_eq`).
  * `normPoly g s` computes the norm `N_s(x) = Res_y(f(y), g(x − s y, y))` of `g ∈ K[x]` by
    interpolation. Over any field where `f` splits it equals `lc(f)^e ∏_θ g_θ(x − sθ)`
    (`normPoly_map`, via `resultant_eq_prod_eval`).
  * `rootsIn g` searches `s` with `N_s` squarefree, factors `N_s` over `ℚ` (Kronecker), and reads
    each root off a linear `gcd_K(g, M(x + sθ))`.
  * Both directions are proved: `rootsIn_sound` (only roots are returned) and `rootsIn_complete`
    (for squarefree `g`, an admissible `s` exists in the search range and every root is returned).
    The proof uses the Galois action on `ℚ̄` (`minpoly.exists_algEquiv_of_root'`) and a collision
    count for the bad shifts `s`.

  With this, **`ellDecideNF`** (`Algebraic/EllDecideNF.lean`) computes the splitting data itself:
  the roots of `D` in `K` and square roots of `p(α)`. `ellDecideNF_spec`: every answer is correct.
  `ellDecideNF_ne_none`: it always answers when `D` is squarefree and splits over `K`, and `p`
  takes non-zero square values there. Kernel-checked examples over `ℚ(√2)`
  (`Algebraic/EllDecideNFExample.lean`): `∫ (2x²+4)/((x²−2)√(x³+2x²−2x))` is elementary and
  `∫ 8/((x²−2)√(x³+2x²−2x))` is not, with all roots found by the kernel. Norms of degree 9 (cubic
  fields) exceed the kernel's memory in practice, so the cubic examples use checked data.


  **Splitting fields and the fully automatic elliptic decision** (`Algebraic/NFAdjoin.lean`,
  `NFSplit.lean`, `Schur.lean`, `GoodPrime.lean`, `EllDecideQ.lean`):
  * `adjoinStep` is Trager's primitive-element step. For `h ∈ K[x]` and an irreducible factor `M` of
    the norm `N_t`, `θ` is recovered in `ℚ[γ]/(M)` as the root of a linear gcd, and `γ − tθ` is a
    root of `h`. Proved: `adjoinStep_sound`, and `adjoinStep_complete` (via the collision lemma).
  * `splitLoop`/`sqLoop`/`splitField` build, from `ℚ = ℚ[x]/(x)`, a number field over which `D`
    splits and `p` is a non-zero square at each root of `D` (`splitField_spec`). Each round adds a
    root (`growStep_spec`) or a square root (`sqLoop_spec`), transported along the embeddings.
  * **Schur's theorem** (`Schur.exists_prime_dvd_eval`, not in Mathlib): a non-constant integer
    polynomial has roots modulo infinitely many primes. Consequence `exists_good_prime`: there is
    an odd prime of good reduction at which the field polynomial has a simple root.
  * `ellDecideQ a b c A D B` puts these together: splitting field, then the first good prime
    `< B`, then `ellDecideNF`. **`ellDecideQ_spec`**: every answer is correct (constants
    algebraically closed). **`ellDecideQ_complete`**: if `D` is squarefree and coprime to `p`,
    every large enough bound `B` gives an answer. So `∫ A dx / (D √(x³+ax²+bx+c))` with simple
    finite poles off the branch points is **decided for every such integrand with rational
    coefficients**, including residue fields of any degree. (Kernel evaluation is practical only
    for small fields; the proofs cover all cases.)
  * **Arbitrary denominators** (`Algebraic/HermiteExistK.lean`, `HermitePolyK.lean`,
    `HermiteBoundK.lean`, `EllDecideGenQ.lean`). The Hermite decomposition on the elliptic curve
    is proved over any field of characteristic zero (`hermite_polyK`, degree bound
    `hermite_deg_boundK`). `ellDecideGenQ a b c A D B` takes any `D ≠ 0` (higher-order poles,
    poles at branch points): with `S` the part of the squarefree part of `D` coprime to `p`, it
    solves `2ADS = S·L_D(W) + 2D²T` over `ℚ` (`linSolve`), which gives
    `A/(Dy) = (W/D·y)′ + T/(Sy)`, then calls `ellDecideQ` on `T/(Sy)`. **`ellDecideGenQ_decides`**:
    for every `D ≠ 0` there is a bound beyond which it answers, and every answer is correct. So
    `∫ A(x) dx / (D(x) √(x³+ax²+bx+c))` with `A, D ∈ ℚ[x]` is **decided in full** (constants
    algebraically closed). Completeness of the linear step: the decomposition exists over `ℚ̄`
    with bounded degrees, so the rational system is solvable (`linSolve_complete_map`).
  The latter is `ell_glue` over the constant field, which already allows arbitrary residues, plus
  the ℚ-basis decomposition. That decomposition needs arithmetic in the Galois closure of the
  residue field: the residue divisors `Σ λ(σ r)·P_σ` are defined only there.
* **Elliptic orbits of degree ≥ 4**: `ellDecideOrbit` is sound but not proved complete (a Cantor
  step can create new non-linear or non-simple factors); this is now superseded by `ellDecideQ` /
  `ellDecideGenQ`, which are complete.

## Coupled Risch systems (in progress)

Needed for the exact part of non-Kummer algebraic integrands: `Y′ + A Y = ∑ cₗ Gₗ` for vectors
`Y ∈ Fₘ(t)ⁿ`. Proved (standard axioms only):

* **Denominators** (`Computable/SysDenG`, `sys_den_bound`): for `A = A₀/q`, every solution has
  denominator dividing `h q^B S` once every natural indicial root at the factors of `q` is
  `≤ B` (`p ∣ det(A₀ − e D(q) I)`, `sys_den_indicial`, `den_local`). `B` is computed
  (`indBound`, `indBound_spec`): the indicial norm `N_{K[t]/(q)} det(A₀ − E q′ I)` is evaluated by
  a computable determinant (`DetF`) and remainders, interpolated (`vandCheck`, `coeff_eq_interp`),
  and its natural roots bounded through `ℚ`-relations and a Cauchy bound (`intRootBound_spec`).
* **Degrees at a primitive level** (`Computable/SysDeg`, `sys_deg_prim`): beyond the right-hand
  side, the degree is a *special degree* (a nonzero constant `c` with `(D η + β) c` a derivative);
  these are bounded by `specBound` (`specBound_spec`: parametric integration per component,
  annihilators, roots of a pencil determinant).
* **The coefficient loop** on codes (`loopC_stage`), vector parametric integration
  (`vecLim_spec`), the final constant filter (`relRun_inv`), assembled in `polySysC`
  (`polySysC_sound`, `polySysC_complete`).
* **Primitive levels** (`Mixed/SysPrim`, `primSysC_sound`, `primSysC_complete`): for `q`, `h`
  monic and `deg A₀ < deg q` (the matrix vanishes at infinity), every rational solution is a
  constant combination of the returned `W/Den`; otherwise the answer is `none`. **In that regime
  the solver always answers** (`primSysC_isSome`, `primSysC_isSome_sq`, `Mixed/SysPrimSome`):
  `q` squarefree, `h` monic, `deg A₀ < deg q`, `η` not a derivative suffice. The bounds were made
  complete for this: the indicial bound (`indBound2`: the indicial norm is not identically zero,
  `indNorm'_ne_zero`; interpolation always valid, `vandCheck_true`; a root bound through
  `ℚ`-coordinates, `intRootBound2`) and the special-degree bound (`specBound2`: Gram determinant of
  the pencil, never identically zero when `η` is not a derivative, `specBound2_isSome`, through
  annihilator duality `ann_dual`).
  Consequently **the exact-part test in a basis answers** (`exactW_isSome`, `Mixed/NKExactWSome`)
  with solver `primSysC` whenever the basis derivation matrix has entries vanishing at infinity
  with squarefree denominators: the executable lcm is monic, a common multiple, and squarefree
  when the inputs are (`lcmGL_spec`, `Mixed/LcmGL`), so the `cofC` checks pass.
  **Known denominators** (`Mixed/SysPrimK`): `primSysB … B` takes the exponent `B` of
  `Den = h q^B` instead of computing it; it is sound, complete for the solutions whose denominator
  divides `h q^B` (`primSysB_complete`), and answers for monic `q`, `h`, `deg A₀ < deg q`, `η` not a
  derivative, with no condition on the factors of `q` (`primSysB_isSome`). `exactWE`
  (`Mixed/NKExactWE`, `exactWE_correct`, `exactWE_isSome`) is the exact test with such a solver
  and an extra denominator bound `E`.
  **Rescaling at infinity** (`Mixed/NKExactWR`): `exactWR` takes a basis `w` with derivation matrix
  `M` and integer shifts `rᵢ`; it bounds the coordinate denominators of any antiderivative by
  `h q^B` (indicial bound in `w`, `sys_den_bound`), passes to `w̃ᵢ = t^{−rᵢ} wᵢ` (matrix
  `M̃ᵢⱼ = t^{rⱼ−rᵢ} Mᵢⱼ − δᵢⱼ rᵢ η/t`, `rescale_deriv`), and runs `exactWE` with
  `E = h q^B t^R`. **It is correct for every basis and shifts** (`exactWR_correct`) and **answers
  whenever the matrix of `w` has squarefree denominators and the rescaled matrix vanishes at
  infinity** (`exactWR_isSome`) — the situation of an integral basis normal at infinity with its
  exponents at infinity as shifts.
  **Existence of such bases** (`Curves/IntBasisLog`, `IntBasisFin`, `IntBasisInf`,
  `IntBasisMain`): for every curve `F(x, y) = 0` over a field of characteristic `0`,
  **`exists_logBasis`** gives a basis `wᵢ` of `C(x, y)` over `C(x)`, shifts `rᵢ ≥ 0`, a squarefree
  `S₀` and polynomials `Pᵢⱼ` with `S₀ wᵢ′ = ∑ Pᵢⱼ wⱼ` and `deg (x^{rⱼ+1} Pᵢⱼ − δᵢⱼ rᵢ x^{rᵢ} S₀) ≤
  rᵢ + deg S₀` (the rescaled matrix vanishes at infinity). Proof: Mathlib's integral closure of
  `C[x]` is free of rank `n` (`exists_intBasis`, `exists_IBasis`); integral ⇔ no finite pole along
  the Puiseux branches (`regularFinite_of_integral`, `integral_of_regular`); logarithmic stability
  `rad(Q) f′` integral when `f′ = W/Q` (`regularFinite_rad_deriv`: `(x − a) d/dx = (T/N) d/dT`) and
  `x d/dx` at infinity (`infOrd_x_deriv`); a reduction descent at infinity (`exists_reduced`,
  terminating since a non-zero integral element has no zero at infinity beyond its pole order,
  `infOrd_nonneg`, via `algebraic_of_regular`) and normality of reduced bases
  (`reduced_normal`).
  **Transfer to a tower level** (constant curves `F₀ ∈ ℚ[t][Y]` over a primitive level):
  `exists_logBasis_scaled` (`Curves/IntBasisScaled`: any derivation with `x′ = e ≠ 0` killing `ℚ`,
  by applying `exists_logBasis` to `e⁻¹ D`), `const_logBasis` (`Mixed/NKConstBasis`: matrices `T`,
  `T⁻¹` of quotients of polynomials over `ℚ` with `S₀ wᵢ′ = η ∑ Pᵢⱼ wⱼ`), `exactTR`
  (`Mixed/NKExactTR`: `exactT` with gcd-reduced entries `redC` and `exactWR`; `exactTR_correct` for
  any `T`, `T⁻¹`, `r`; `exactTR_isSome` in the regime, `Mixed/NKExactTRSome`), **`exactTR_exists`**
  (`Mixed/NKExactTRExists`: codes `matQ` and shifts for which `exactTR` answers; `θ′` computable
  since `P` is the minimal polynomial, `sep_P_const`), the complete search `searchTR`
  (`Mixed/NKSearchTR`: an `Encodable` enumeration of candidates; sound, and answering for every large
  bound, `searchTR_complete`) and **`nk_decidesTR`** (`Mixed/NKDecidesTR`, with `nk_iffTR`,
  `Mixed/NKLogDecideTR`): **for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a logarithmic level with constant
  coefficients `aᵢ ∈ ℚ[t]` and a single place at infinity, `∫ ∑ bⱼ θʲ` is decided for every large
  bound, with no basis, shift or certificate supplied** (the trace part by `elM`).
  **Exponential levels** (`t′ = a′ t`): `expSysB` (`Mixed/SysExpB`: known denominator `h q^B`,
  rational triangular limit at infinity; sound, complete, answering), the place `t = 0` without
  triangularization (`Computable/SysDenAnn`: `A₀(0) = q(0) a′ Λ₀` with `∏_{k<N₀} (Λ₀ − k/N₀) = 0`
  bounds the pole order at `0` by that of the right-hand side, via Lagrange idempotents),
  `exactWRE` (`Mixed/NKExactWRE`: rescaling `t^{rⱼ−rᵢ} Mᵢⱼ − δᵢⱼ rᵢ a′` and conjugation by a
  constant rational `C`; `exactWRE_correct` for all parameters, `exactWRE_isSome`), `exactTRE`
  (`Mixed/NKExactTRE`, `NKExactTRESome`). The residue matrices of an integral basis are
  annihilated by `∏_{k<n!} (X ∓ k/n!)` at `x = 0` and at infinity (`Curves/IntBasisAnn`:
  `resid0_ann`, `resInf_ann`; the Puiseux exponents have denominators `≤ n` because `T ↦ ζT` with
  `ζᴺ = 1` permutes the roots, `Curves/LScale`: `branch_support`), so `Λ∞` is diagonalizable over
  `ℚ` (`Mixed/QDiag`: `exists_diag_of_ann`) and `exists_logBasisA`/`const_logBasisG` give
  **`exactTRE_exists`** (`Mixed/NKExactTREExists`). With the complete search `searchTRE`
  (`Mixed/NKSearchTRE`) and `nk_iffTRE`: **`nk_decidesTRE`** (`Mixed/NKExpDecideTRE`): **for
  constant curves over an exponential level with single places above `t = 0` and `t = ∞`,
  `∫ ∑ bⱼ θʲ` is decided for every large bound, with no basis or certificate supplied** (with
  precomputed candidates first: `searchTREP`/`nk_decidesTREP`; `Mixed/NKDecidesTREExamples`: on
  `θ³ + tθ = t + t²` over `eˣ` the power basis with shifts `(0, 1, 2)`, `N₀ = 3` and the reversing
  permutation answers at bound `0`: `∫ θ dx` is not elementary, `∫ θ′ = θ`).
  **Parametric versions** (is `f − ∑ cᵢ gᵢ` exact for some constants, as needed with several
  places at infinity): `exactWEL` (`Mixed/NKExactWEL`), `exactWRL` (`Mixed/NKExactWRL`),
  `exactWREL` (`Mixed/NKExactWREL`), the generic `exactTGL` with `exactTRL`, `exactTREL`
  (`Mixed/NKExactTGL`), all correct for every parameter, answering in the same regimes
  (`Mixed/NKExactTRLSome`) and with existing parameters for constant curves
  (`Mixed/NKExactTRLExists`); complete searches `searchTRL`, `searchTREL` (`Mixed/NKSearchTRL`).
  Hence **`nk_decidesRNTR`, `nk_decidesETRNTRE`** (`Mixed/NKInfRNTR`): with several places at
  infinity (units over `ℚ(α)` supplied, as in `nk_iffRN`, `nk_iffETRN`) the exact part needs no
  supplied basis for constant curves.
  **Non-constant coefficients over a logarithm (Risch's mixed case, one place at infinity).** For
  `θⁿ + ∑ aᵢ(t) θⁱ = 0` with `aᵢ ∈ Fₘ[t]` arbitrary codes (a curve over `Fₘ(t)` whose derivation is
  non-trivial on `Fₘ`) and the weighted shape of `nkShape`, the limit of the rescaled derivation
  matrix at infinity is no longer `0`: it acts on the residue algebra through the coefficient
  derivation. The pieces: a system solver with a non-zero limit matrix `Λ` (`primSysBL`,
  `Mixed/SysPrimL`; degree bound `specBoundL` from a Gram determinant plus the `ℚ`-relations of the
  homogeneous solutions, `Mixed/SysSpecialL`, `Computable/RatProj`), with the triangular solver one
  level down after checking `Λ` triangular with logarithmic-derivative diagonal (`primSysV`,
  `Mixed/SysPrimV`); the tests `exactWRV`/`exactTV` and the decision `nk_iffTV`
  (`Mixed/NKLogDecideTV`, no constant-curve hypothesis); finite places with a coefficient
  derivation (`regularFinite_rad_derivW`, `Mixed/IntBasisLogW`); the place at infinity by weights,
  without Puiseux expansions (`root_lead_inf`, `eval_lead_inf`, `Mixed/NKInfLead`): along any branch
  the first `N` coefficients are differentiated coefficientwise, so the expansion matrix satisfies
  `A′ = Λ A` with independent rows, `Λ` is triangular in the order of the weights with diagonal
  `(j₀/n) c′/c` (`nk_inf_struct`, `Mixed/NKInfStruct`), and the limit system is non-degenerate
  because `η` is not a derivative in the algebraic closure (`nondeg_of_gauge`); echelon integral
  bases at the single place at infinity (`exists_echelon`, `Mixed/NKEchelon`;
  `exists_nkBasis`, `Mixed/NKBasisExists`), taken over the field of code values
  (`nkCurveQ`, `Mixed/NKCodeField`) so that codes exist; `exactTV_exists`
  (`Mixed/NKExactTVExists`); a complete search over all codes (`searchTV`, `Encodable` codes) and
  **`nk_decidesTV`** (`Mixed/NKDecidesTV`): `elM` and `searchTV` decide whether
  `∑ bⱼ(t) θʲ` has an elementary integral, nothing supplied. Example (`Mixed/NKDecidesTVExamples`,
  candidate `nkCandV` from the shape, `#guard`): for `θ³ + θ = x log x`, `∫ θ′ = θ` and **`∫ θ dx`
  is not elementary**.
  **Non-constant coefficients over an exponential** `t = eᵃ` (single place at infinity, `nkShape`,
  and single place above `t = 0`, `nkShape0`): at infinity the branch derivation is
  `δ − (a′/N) s d/ds`, so the limit is triangular with diagonal `p a′ + q c′/c`
  (`nk_inf_struct_exp`, `exists_nkBasisE`, `Mixed/NKExpCurve`); the system solver `expSysV`
  (`Mixed/SysExpV`; degree bound `sys_deg_triV`: special degrees only at `k = −pᵢ` by transcendence
  of `eᵃ`); at `t = 0`, a finite place of the integral basis, poles of solutions are excluded by a
  runtime-checked gauge `C, C⁻¹` making `C M(0)ᵀ C⁻¹ − C′ C⁻¹` triangular with diagonal
  `p₀ a′ + q₀ c′/c`, `p₀` not a positive integer (`sys_den_zero_gauge`, `Computable/SysDenTV`;
  `zeroOKV`, `exactWREV`, `Mixed/NKExactWREV`). The gauge exists: the elements `yʲ/t^{⌊jd₀/n⌋}`
  are integral, of orders `(jd₀ mod n)/n` above `0` (`root_lead_zero`, `Mixed/NKExp0Lead`); their
  coordinates at `0` are invertible and give the triangular `Λ₀ = (U′ + U M(0)) U⁻¹` with diagonal
  `((jd₀ mod n)/n) a′ + j c′/(n c)`, `c = tc(a₀)` (`exists_gauge0`, `Mixed/NKExp0Gauge`). Then
  `nk_iffTEV` (`Mixed/NKExpDecideTEV`), `exactTEV_exists` (`Mixed/NKExactTEVExists`) and
  **`nk_decidesTEV`** (`Mixed/NKDecidesTEV`, complete search `searchTEV` over all codes):
  decided, nothing supplied. Example (`Mixed/NKDecidesTEVExamples`, `#guard`): for `θ² = x eˣ`,
  `∫ θ′ = θ` and **`∫ √(x eˣ) dx` is not elementary**.
  **Several places at infinity for non-constant coefficients** (logarithmic level): for any
  curve, units at the finite places have order sum `0` along a branch system above infinity
  (`unit_sum_inf`: the norm is a constant), so if that system has `n` roots and `n − 1` given units
  are multiplicatively independent modulo `Fₘ`, every unit is a power product of them up to
  constants (`mem_pow_units_inf`, `Mixed/NKUnitsInf`) — no certificate for the places is needed;
  geometric irreducibility of a curve with coefficients in `Fₘ[t]` comes from an Eisenstein
  certificate at a separable common factor (`eisCk`, `irreducible_map_of_eis`,
  `Mixed/NKEisGeo`); the exact part with logarithmic-derivative parameters in a rescaled basis
  (`exactWLE`, `exactWRVL`, `exactTLV`); **`nk_iffInfV`** (`Mixed/NKInfRV`): `∫ f` is elementary
  iff `f − τ(f)/n − ∑ cᵢ uᵢ′/uᵢ` is exact for some constants and `∫ τ(f)/n` is elementary. Example
  (`Mixed/NKInfRVExample`, `#guard`): `θ² = log² x + x`, unit `u₀ = −(θ + log x)²/x`:
  **`∫ √(log² x + x) dx` is not elementary**. Over an exponential level with a single place above
  `t = 0` the same holds (**`nk_iffETInfV`**, `Mixed/NKInfRVExp`; `unit_pow_expU_inf`,
  `nk_liouvilleEU_inf`, `Mixed/NKUnitsInfExp`; exact part `exactWREVL`/`exactTLEV` with the
  gauge at `0`); example (`Mixed/NKInfRVExpExample`): `θ² = e²ˣ + x eˣ`, unit
  `u₀ = −4 (θ + eˣ + x/2)²/x²`, **`∫ √(e²ˣ + x eˣ) dx` is not elementary**.
  **Completeness for curves split at infinity** (logarithmic level): when the leading polynomial
  `L(Z) = ∑ [aᵢ]_{(n−i)s} Zⁱ` has `n` distinct roots in `Fₘ` (`splitShapeC`), the values `A` at the
  places at infinity of the rescaled integral basis form an invertible matrix with `A′ = Λ A`
  (`split_gauge`, `Mixed/NKSplitGauge`: branches through the powers of `y/xˢ`, Vandermonde, a
  power-series inverse; `leadPoly_eq_prod`, `Mixed/NKSplitInf`), so the limit matrix is
  gauge-trivial over the code values; the solver accepts a runtime-checked gauge at infinity
  (`primSysVG`, `sysSpecAt_gauge`, `Mixed/SysPrimVG`), and `exactTLVG` answers for the gauge `Aᵀ`
  (`exactTLVG_exists`, `Mixed/NKExactTLVGExists`; the limit system is non-degenerate because the
  gauge trivializes it and `η` is not a derivative). **`nk_decidesInfVG`** (`Mixed/NKDecidesInfVG`):
  for such curves with `n − 1` independent units, `elM` and a complete search over all codes
  (units, basis, shifts, gauge) decide `∫ ∑ bⱼ θʲ`. **The same completeness over an exponential
  level** (single place above `t = 0`): any coupled-system solver can be put behind a
  runtime-checked constant gauge (`gaugeSolver`, `gaugeSolver_spec`, `Mixed/SysGauge`: the gauged
  system `C A₀ C⁻¹ − q C′ C⁻¹`, `sysSol_gauge`, `gaugeA_inv`, limit `gaugeA_lim`); the exact-part
  tests take any solver meeting the specification (`exactWREVLS`, `exactTLEVS`), and with the
  gauged `expSysV` (`expSysVG`, `exactTLEVG`, `Mixed/NKExactTLEVG`) they answer for the gauge
  `Aᵀ` at infinity and the gauge of `exists_gauge0` at `0` (`split_gaugeE`, `exists_nkBasisEG`,
  `Mixed/NKSplitGaugeE`: above infinity `x′ = a′x` acts on the coefficient of `T⁰` as the
  coefficient derivation; `exactTLEVG_isSome`, `exactTLEVG_exists`); **`nk_iffETInfVG`**
  (`Mixed/NKInfRVExpG`) and **`nk_decidesETInfVG`** (`Mixed/NKDecidesETInfVG`): `elM` and a
  complete search (units, basis, shifts, both gauges) decide `∫ ∑ bⱼ θʲ`. **The data are
  computed** (`Mixed/NKSplitCand`, untrusted, re-checked by the kernel checks): branches at the
  places at infinity over the code field (`expandInfS`), units as kernels of the linear conditions
  `ord_{Pₖ} u ≥ cₖ` (`unitSearchS`, Gauss–Jordan over any code field `rrefO`), normalized to norm
  `1` (`uⁿ/N(u)`, so that `τ(u′/u) = 0`), logarithmic derivatives and the independence
  certificate (`splitUnits`), basis `θʲ/t^{⌊j d₀/n⌋}`, the Vandermonde gauge at infinity and the
  sorting permutation at `0` (`splitCandsL`, `splitCandsE`); `searchIVGP`/`searchETVGP` try them
  before enumerating (**`nk_decidesInfVGP`**, **`nk_decidesETInfVGP`**). Examples
  (`Mixed/NKSplitCandExamples`, `#guard`, nothing supplied by hand): the searches answer at
  bound `0` — **`∫ √(log² x + x) dx`** and **`∫ √(e²ˣ + x eˣ) dx`** are not elementary.
  **Ramified places at infinity** (a single slope `s'/e`, `gcd(s', e) = 1`, residual polynomial
  `∏ₖ (Zᵉ − γₖ)` with distinct `γₖ ∈ Fₘ`, `ramShapeC`): the leading values of the branches at a
  fractional slope (`leadPolyR_eq_prod`, `Mixed/NKRamLead`); roots with the same `e`-th power of
  their leading value are rotations `T ↦ ζT` of each other, so all functions have the same orders
  along them, and `n/e − 1` independent units span the units (`rot_class`, `cover_ram`,
  `mem_pow_units_cls`, `unitsSpan_ram`, `Mixed/NKRamUnits`; the Liouville-form theorems now take
  any `UnitsSpan`); `nk_iffInfVR`/`nk_iffETInfVR` (`Mixed/NKInfRVR`, `NKInfRVExpR`). Completeness:
  the basis is expanded in the monomials `θʲ/x^{⌈j s'/e⌉}` (bounded coefficients through a
  Vandermonde matrix in the distinct leading values, `bounded_ram`, `Mixed/NKRamExpand`; values at
  infinity invertible by normality, `ram_binf`); the jets `[T^{N'h}]` along one root per place give
  `T Z = Z′ − Z D` for a level-triangular `Z` (`tri_of_TZ`, `Mixed/NKRamAlg`), so a constant gauge
  (a level-graded Vandermonde matrix) makes the limit level-triangular with diagonal
  `(t/e) γₖ′/γₖ` (log) or `(t/e) γₖ′/γₖ − (R/e) a′` (exp) (`ram_gauge`, `ram_gaugeE`), and the jets
  make the log limit system non-degenerate (`nondeg_of_gauge'`); `exactTLVG_exists_ram`,
  `exactTLEVG_exists_ram` (`Mixed/NKRamExists`, `NKRamExistsE`); **`nk_decidesInfVR`**,
  **`nk_decidesETInfVR`** (`Mixed/NKDecidesInfVR`, `NKDecidesETInfVR`): with `n/e − 1` units the
  procedure decides. **Computed candidates** (`Mixed/NKRamCand`): the units come from the split
  subcurve `φ = θᵉ` when `P = M̃(θᵉ)` (`ramUnits`: `splitUnits` on `φ`, lifted), the basis `θʲ`
  with level shifts, and the level-graded Vandermonde gauge (`ramGaugeC`, `ramCandsL`,
  `ramCandsE`); **`nk_decidesInfVRP`**, **`nk_decidesETInfVRP`**. Examples
  (`Mixed/NKRamCandExamples`, `#guard`, about 1.5 minutes per search): **`∫ (log² x + x)^{1/4} dx`** and
  **`∫ (e²ˣ + x eˣ)^{1/4} dx`** are not elementary, while `∫ θ′` is found elementary. (A
  performance note: Lean's compiler eta-expands a definition whose value is a function, so
  `vecM`-style memoization inside such a definition recomputes on every access. Matrices that are
  accessed repeatedly are therefore passed as data (`matFn (matData …)`, `Mixed/SysPrimL`), which
  took this example from more than 28 minutes to under 2.)
  **Several places above `t = 0`** (exponential levels; previously a single totally ramified place
  was required, `nkShape0`): the logarithmic derivatives are regular above `t = 0`, so the logarithms
  of a Liouville form are S-units for `S` = the places at infinity and above `0`. For such units
  `N₀ ∑_∞ ord + N ∑_0 ord = 0` (`unit_sum_inf0`), and `x` with `m` independent S-units, `m + 2` the
  number of roots above infinity and `0`, span the S-units (`mem_pow_units_inf0`, Cramer step
  `pow_units_cramer`, `Mixed/NKUnitsInf0`); `nk_liouvilleEU_span0` (`Mixed/NKUnitsInfExp0`) needs no
  condition at `0`. Units are certified as `U/tʲ` with `U V ≡ tᵏ` and `g tᵏ + j a′ tᵏ ≡ U′ V`
  (`unitsC0`, so norm-`1` normalizations are allowed), independence by a generalized Wronskian
  (`indepWC`: positions and derivative orders with an inverse; `indepC` cannot certify more than
  `n − 1` units), `Mixed/NKUnits0Decide`; **`nk_iffETInf0`** (`Mixed/NKInf0Exp`). Completeness for
  a fibre `F(0, Y) = ∏ (Y − βₖ)` with distinct `βₖ ∈ Fₘ` (`split0C`): the Hensel branches above `0`
  and the Lagrange elements of the fibre give a gauge at `0` whose limit vanishes
  (`exists_gauge0_split`, `Mixed/NKExp0Split`), `exactTLEVG_exists0`; **`nk_decidesETInf0`**,
  `nk_decidesETInf0P` (`Mixed/NKDecidesETInf0`, `NKSplit0Cand`). Example (`Mixed/NKSplit0Examples`):
  `split0CandsA` finds the S-units (kernels of order conditions at infinity and along the Hensel
  branches above `0`, `unitSearch0S`, normalized to norm `1`), the logarithmic derivatives, the
  Wronskian certificate and both gauges — only the leading values `±1` and the fibre roots `±x` are
  given: **`∫ √(e²ˣ + x eˣ + x²) dx` is not elementary** (about 20 s), `∫ θ′` is found. Still
  open there: ramified or non-rational places above `0` among several. (The Wronskian
  certificate always exists when the units' logarithmic derivatives are independent:
  `nk_decidesETInf0PW`, see below.)
  **A ramified place at infinity with several places above `0`** (`Mixed/NKUnitsCls0`,
  `NKInf0ExpR`, `NKRamExistsE0`, `NKDecidesETInf0R`, `NKRam0Cand`): S-units are spanned when the
  roots above infinity and above `0` are covered by classes with equal orders (`mem_pow_units_cls0`,
  rows = class representatives, the last class forced by the product formula; `unitsSpan0_ram` with
  the rotation classes `cover_ram`); **`nk_iffETInf0R`**, `exactTLEVG_exists_ram0` (ramified gauge
  at infinity, Lagrange gauge at `0`), **`nk_decidesETInf0R`**, `nk_decidesETInf0RP`; `ram0Cands`
  finds the S-units for a single ramified place at infinity (`findUnit0R`: monomials of bounded
  order at infinity, Hensel branches above `0`, norm by the determinant of the multiplication
  matrix). Example (`Mixed/NKRam0Examples`, a few seconds): **`∫ √(x eˣ + 1) dx` is not
  elementary**, `∫ θ′` is found; with a base change (`nk_decidesETInf0RP_bc`, `Mixed/NKBC0R`,
  `NKBC0RExamples`, over `w² = x`): **`∫ √(x eˣ + x) dx` is not elementary**; and on a curve of
  genus `1`, where the S-unit comes from a `3`-torsion point (`θ² = t³ + w²`, the flexes
  `(0, ±w)`): **`∫ √(e³ˣ + x) dx` is not elementary** (seconds, `#guard`). (Square roots of
  odd degree in `eˣ` such as these are also within the scope of `keDecide`, which decides the torsion
  question by an oracle; the point of the `NK` route is that it applies to any `θⁿ + ∑ aᵢ θⁱ`, given
  the S-units. The split examples of even degree are not covered by `keDecide`.)
  **Non-rational places through a base change** (`Mixed/NKBC`): when the residual roots (`γₖ` at
  infinity, `βₖ` above `0`) are algebraic over the base `F₀`, changing the base curve to one whose
  function field contains them (`MTower.base_change`, as for `kzDecide_bc_correct`) makes the places
  rational; `bc_decides` transfers any decision over the new tower (translated codes) to the
  original integral along the algebraic extension, giving **`nk_decidesETInf0P_bc`**,
  `nk_decidesETInfVGP_bc`, `nk_decidesInfVGP_bc`, `nk_decidesETInfVRP_bc`, `nk_decidesInfVRP_bc`.
  Example: `θ² = x e²ˣ + eˣ` has leading values `±√x` at infinity; over `w² = x` the search answers in
  seconds (`#guard`): **`∫ √(x e²ˣ + eˣ) dx` is not elementary**, `∫ θ′` is found. Example (`Mixed/NKBCExamples`):
  `θ² = e²ˣ + x eˣ + x` has a single place above `t = 0` with residue field `ℚ(x)(√x)`; over the base
  `w² = x` all certificates are checked by `#guard` and the S-units are found; the search
  (about 10 minutes, run by `#eval`, documented in the file) answers `some false`:
  **`∫ √(e²ˣ + x eˣ + x) dx` is not elementary**. This covers residue fields generated over `F₀`;
  residue fields that are algebraic over `Fₘ` but not over `F₀` (for `m > 0`) are not covered.
  **Practicality beyond the first level:** all examples above live at the first level over `ℚ(x)`.
  At higher levels (e.g. `θ² = t₁² + t₀t₁ + t₀²` with `t₀ = eˣ`, `t₁ = e^{t₀}`) the candidate
  generators find the units (about 3 minutes, with normalized arithmetic in the expansions), but
  the logarithmic derivatives and the search did not finish within 20 minutes: nested fractions of
  codes swell without normalization and are expensive to normalize. A representation with cleared
  denominators would be needed; the theorems themselves are stated for any level.
  **Independence certificates are no longer inputs.** `indepC gls J H` is now the generalized
  Wronskian `indepWC gls J D H` whose derivative orders `D` are the entries of `J` after the first
  `k = #gls` (`J` of length `k`: the plain minor, so all earlier certificates are unchanged).
  **Wronskian certificates exist** (`exists_wronsk`, `indepWC_exists_of_logs`,
  `Mixed/NKWronskExists`: the columns `((gᵢⱼ)^{(d)})ᵢ` span, else a minimal-support relation
  normalizes to a constant one) whenever the logarithmic derivatives `gᵢ` are linearly independent
  over the constants of the code field modulo `Fₘ₊₁`. Hence `nk_decidesInfVGPW`,
  `nk_decidesETInfVGPW`, `nk_decidesInfVRPW`, `nk_decidesETInfVRPW`, `nk_decidesETInf0PW`,
  `nk_decidesETInf0RPW` (`Mixed/NKWronskDecide`) take only `unitsC`/`unitsC0`-certified units with
  that independence (a mathematical hypothesis; the search finds the certificate). **Multiplicative
  independence suffices** (`Mixed/NKMultLin`, `Mixed/NKDecidesPM`): the constants among the code
  values are rational (`codeVals_const_rat`: at the base a constant `W(x, y)/Q(x)` with
  `deg_y W < n` is a constant polynomial by the minimality of the curve equation, and over each
  level `P(t)/Q(t)` constant forces `P = cQ` by transcendence), so a relation `∑ cᵢ uᵢ′/uᵢ = f ∈
  Fₘ₊₁` is rational, has `f = 0` by the trace (`trace_kill`: the rows have zero trace, `s₀ = n`),
  and clears to `∏ uᵢ^{aᵢ}` constant (`rat_logDeriv_rel`); hence `hli_of_mult` (`unitsC`) and
  `hli_of_mult0` (the S-units `uᵢ t^{−jᵢ}` of `unitsC0`), and the decisions
  `nk_decidesInfVGPM`, `nk_decidesETInfVGPM`, `nk_decidesInfVRPM`, `nk_decidesETInfVRPM`,
  `nk_decidesETInf0PM`, `nk_decidesETInf0RPM` assume only certified units that are
  multiplicatively independent modulo the constants. Still not formalized: that the units
  themselves exist (full rank of the S-unit group — otherwise this is the non-torsion case), and
  the analogue for `indepCN` over `ℚ(α)` (`NKInfRN`).
  Still open for non-constant coefficients: curves *without* enough units (a
  non-torsion question for the places at infinity, or the residue approach), places at infinity
  with residue fields larger than `Fₘ` not generated by elements algebraic over `F₀` (several
  slopes are decided: `nk_decidesInfVMR`, `nk_decidesETInfVMR`, `nk_decidesETInf0MR`, and with
  `nk_decidesInfVMRPM`, `nk_decidesETInfVMRPM`, `nk_decidesETInf0MRPM` assuming only certified
  multiplicatively independent units). In all these searches
  the enumeration is only the fallback that makes the procedure complete; computed candidates are
  tried first (above for split curves; `searchTRP`/`nk_decidesTRP` with the basis normal at
  infinity `nkTc` for a single place), and a candidate generator that provably always succeeds is
  not formalized (`Mixed/NKDecidesTRExamples`: on `θ³ + tθ = t²` over `log x` the search
  answers at bound `0`: `∫ θ dx` has no exact part, `∫ θ′ = θ`).

* **Exponential levels** (`Mixed/SysExp`, `expSysC_sound`, `expSysC_complete`): `t = exp a`, for
  `A₀` vanishing at `t = 0` and `deg A₀ < deg q`, `q(0) ≠ 0` (checked): the special place `t = 0` is
  bounded by the right-hand side (`sys_den_zero`, using that `z′ + j a′ z = 0` has no nonzero
  solution), the degree by `sys_deg_exp`, and the stages one level down are diagonal Risch
  equations solved componentwise (`vecRde_spec`). Examples: `Mixed/SysExpExamples`.

* **Exact part over non-Kummer extensions of a logarithm** (`Mixed/NKExact`, `exactC_correct`): for
  `θ` a root of any monic `P(t, Y)` over a primitive level (powers of `θ` independent), `exactC`
  decides whether `f = ∑ fⱼ θʲ` has an antiderivative `∑ Yᵢ θⁱ` in `Fₘ(t)(θ)`: `θ′` from a Bezout
  identity for `P, P_Y`, the derivation matrix of the power basis, and `primSysC`. Example
  (`Mixed/NKExactExamples`): `θ³ − θ − log x = 0`, `∫ θ′ = θ` found, `∫ θ` proved not in the field.
  The same over an exponential level (`exactCE`, `exactCE_correct`), within the regime of
  `expSysC`, and with a rational upper triangular limit `a′Λ` at infinity (`exactCT`,
  `exactCT_correct`, over `expSysT`: special degrees from the diagonal of `Λ`, `sys_deg_tri`;
  triangular systems one level down by back-substitution, `triSys_spec`; rational exponents,
  `hom_rat`). Example: `θ³ − θ − eˣ = 0`, `∫ θ′ = θ` found, `∫ θ` proved not in `ℚ(x, eˣ, θ)`.
  At `t = 0` the matrix may have a rational triangular limit `a′Λ₀` without positive integer
  diagonal entries (`zeroOK`, `sys_den_zero_tri`: a pole of order `e` at `t = 0` forces
  `Λ₀ᵢᵢ = e`). Example: `θ³ − θ² − eˣ = 0` (ramified above `t = 0`, `Λ₀` with diagonal
  `0, 1/2, 0`): `∫ θ′ = θ` found, `∫ θ` proved not in `ℚ(x, eˣ, θ)`.
* **Separate denominators** (`Mixed/NKExactG`, `exactG`, `exactG_correct`): one correctness proof
  for any system solver meeting `SolverSpec` (instances `primSpec`, `expSpec`, `expTSpec`), with
  the derivation matrix cleared by its own denominators `q` and the integrand by `h`, so that
  multiple poles of `f` at places where the matrix is regular no longer make the indicial norm
  vanish. Example (`Mixed/NKExactGExamples`): over `θ³ − θ − log x`, `1/log² x` proved to have no
  antiderivative in `ℚ(x, log x, θ)`, `(1/log x)′` found exact.
* **Any basis** (`Mixed/NKExactW`, `exactW_correct`; `Mixed/NKExactT2`, `exactT`, `exactT_correct`):
  the exact test in a basis `w = T θ` (`T` and `T⁻¹` supplied as codes, both products checked;
  derivation matrix `(T′ + T M) T⁻¹`). With an integral basis the double poles with singular
  leading matrix of the power basis at singular points of the curve disappear. Example
  (`Mixed/NKExactT2Examples`): `θ² + t θ − t³ = 0` (singular at `t = 0`), basis `(1, θ/t)`:
  `∫ θ′ = θ` found, `∫ θ` proved not in `ℚ(x, log x, θ)` (the power basis gives `none`).
* Integer-root bounds are refined to the actual natural roots below the Cauchy bound
  (`maxRootLE`), which keeps the loops short.

* **Full decision for non-Kummer `θ` over a logarithmic level, single place at infinity**
  (`Mixed/NKLog`, `Mixed/NKLogDecide`, `nk_iff`, `nk_decides`): `θⁿ + ∑ aᵢ(t) θⁱ = 0` with
  `deg a₀ = d`, `gcd(n, d) = 1`, `n deg aᵢ < d (n − i)` (`nkShape`), and `f = ∑ bⱼ(t) θʲ`
  (polynomial coordinates, so no finite poles). Then `∫ f` is elementary iff `f − τ(f)/n` is exact
  in `Fₘ(t)(θ)` (`exactC`) and `τ(f)/n ∈ Fₘ(t)` has an elementary integral (`elM`), where `τ` is a
  trace functional supplied as codes `s` and checked by `traceC` (`s₀ = n`, `∑ⱼ Mᵢⱼ sⱼ = sᵢ′`).
  The proof: the root orders above infinity (`root_order_inf`), the weighted order of `W(x, y)`
  is branch-independent (`eval_order_inf`), the curve is irreducible over any constant field
  (`irr_of_weights`), units without finite zeros are constants (`mem_const_of_unit_inf`), so the
  logarithms of a Liouville form lie in `Fₘ` (`logs_in_base_inf`, `nk_liouville`), and the
  trace splits off the log part (`trace_split`). Example (`Mixed/NKLogExamples`):
  `θ³ − θ − log x = 0`, **`∫ θ` is not elementary**; `∫ 1` passes the exact test.
* **Residue-free finite poles** (`Mixed/NKLogRes`, `nk_iffR`, `nk_decidesR`): `f = ∑ bⱼ(t) θʲ / D(t)`
  with `D` squarefree and a certificate `Bᵏ ≡ U D mod P` (`resCert`, checked), so that `B`
  vanishes at every point above a root of `D` and `f dx` has no pole there. Along each branch the
  integrand then has order `≥ 1 − N` (`logs_zero_branchR`), the logarithms are still constants
  (`logs_in_base_infR`), and the same criterion holds with `exactG` for the exact part. Example
  (`Mixed/NKLogResExamples`): over `θ³ − θ − log x`, **`∫ (θ² − (3/2) log x · θ − 2/3)/(27 log² x − 4)
  dx` is not elementary** (poles at the ramified places, `k = 2`).
* **Non-zero residues with a logarithm certificate** (`Mixed/NKLogCert`, `nk_iffC`): given
  `(uⱼ, cⱼ)` (`uⱼ ∈ Fₘ₊₁[θ]`, `cⱼ ∈ ℚ`) with `f − g − ∑ cⱼ uⱼ′/uⱼ ≡ 0 mod P` (`logCert`, with
  `uⱼ′/uⱼ` computed from `θ′` and a Bezout inverse) and `g` residue-free (`resCert`), `∫ f` is
  elementary iff `∫ g` is, decided as above — in both directions. Example
  (`Mixed/NKLogCertExamples`): **`∫ (θ + θ′/θ)` is not elementary** over `θ³ − θ − log x`. The
  certificate is exactly a torsion witness for the residue divisors; when none is supplied (or
  none exists, the non-torsion case) the answer is still open.
  **Irrational residues** (`Mixed/NKLogCertN`, `nk_iffCN`): the coefficients may lie in a number
  field `ℚ(α)` (`α` a root of a monic `μ ∈ ℤ[X]`; `nk_iffCN'` needs no root among the constants:
  it passes to the splitting field of `μ`, a finite extension, via `exists_lift` and
  `hasElementaryIntegral_finite_iff`) and the logarithms
  are `N`-codes `∑ αᵏ Aₖ(θ)` (`logCertN`: inverses modulo `P` with coefficients in `Fₘ₊₁`, the
  logarithmic derivatives `logDerChkN`, and the identity as an `N`-code modulo `μ` and `P`).
  Example (`Mixed/NKLogCertNExamples`): over `θ³ − θ − log x`, with `α = √2`, `u = θ ∓ α`,
  **`∫ (θ + 4θ′/(θ² − 2))` is not elementary** (residues `±√2`).
  **Found automatically** (`Mixed/NKSearchN`, untrusted, checked by `logCertN`): the search
  runs over `N`-codes (`nOps`: number-field arithmetic over any code field, inverse by Gaussian
  elimination), splits the residues into their `αᵏ`-coordinates and searches one Riemann–Roch
  element per coordinate (`findCertN`). Example (`Mixed/NKSearchNExamples`): on
  `θ² = t³ + t + 19/2`, `t = log x`, `f = θ + √2 (u₁′/u₁ − u₂′/u₂)` (tangent lines over `ℚ(√2)`,
  residues `±2√2, ±√2`) — given only `f` and the fibres over the poles, the certificate is found
  and **`∫ f` is proved not elementary** (about 3 min).
* **Automatic certificates** (`Mixed/NKSearch`, untrusted search, output checked by `logCert`,
  `resCert`): Newton branches at the `Fₘ`-rational points above the poles (`branchSer`), the
  residues (`resAt`, required rational), and the minimal-weight element of the Riemann–Roch space
  with the prescribed orders (`searchW`, Gaussian elimination over codes) give `(u, c)` and the
  residue-free `g`. Example (`Mixed/NKSearchExamples`): for `θ + 2θ′/θ − ½(θ−1)′/(θ−1)` the search
  finds `c = ½`, `div u = 4(0,0) − (0,1) − 3∞`, and `∫ f` is proved not elementary with no
  certificate given by hand. Limits: poles at unramified points over `Fₘ` or `Fₘ ⊗ N` (given as hints),
  residues in `ℚ` (`findCert`) or a number field `N` (`findCertN`), and torsion divisors
  (non-torsion still undecided).
* **The trace test** (`Elementary/TraceDeriv`, `Mixed/NKTrace`, `nk_trace_nec`, `nk_trace_decides`):
  for a finite extension of differential fields in characteristic `0`, `Tr(z′) = Tr(z)′` and
  `Tr(u′/u) = N(u)′/N(u)` (`trace_deriv`, `trace_logDeriv`, via embeddings into `K̄`), and
  `Tr(θⁱ)` is computed in the power basis (`PowerBasis.trace_gen_pow`, codes `traceCodes`). Hence
  for **any** `f = ∑ fⱼ θʲ` (any poles and residues): if `∫ f` is elementary so is `∫ Tr(f)/n`, and
  `elM` proving the latter non-elementary proves `∫ f` non-elementary. Example
  (`Mixed/NKTraceExamples`): **`∫ θ²/(log x − x) dx` is not elementary** over `θ³ − θ − log x`
  (non-zero residues, no certificate). The test holds at logarithmic and exponential levels
  alike: over `θ³ − θ − eˣ`, **`∫ x θ²/(eˣ − 1) dx` is not elementary**.
* **Non-torsion residue divisors** (`Mixed/NKTorsion`, `Mixed/NKNonTors`, `nk_not_elementary`):
  for a Liouville form `f = v′ + ∑ dⱼ wⱼ′/wⱼ` on the curve over `Fₘ` and a good place, the residue
  fixes the orders: `∑ dⱼ ord wⱼ = ρ` (`sum_ord_eq_res`). Projecting by a `ℚ`-linear
  `Λ : Fₘ → ℚ` gives a function `γ = ∏ wⱼ^{M Λ(dⱼ)}` (times powers of `t − αⱼ`)
  with `div γ ≥ M Γ − M c ∞ₓ` whenever `Γⱼₖ = s Λ(ρⱼₖ) + eⱼ` (`divGEU_of_liouville`). Simple poles
  are expanded along unramified branches (`embG_simple_pole`: `(B/D)₋₁ = B(α, y₀)/D′(α)`). The
  non-torsion certificates over a computable field `F` embedded in the constants
  (`not_torsion_of_cert_map`) then refute every Liouville form. The theorem covers curves defined
  over `ℚ` at a logarithmic level with one place at infinity, integrands `η B(t, θ)/∏(t − αⱼ)`
  (`B` over `ℚ`, `αⱼ` and the fibres `yⱼₖ` in `F`), residues `ρⱼₖ ∈ F` (possibly irrational) and
  any `ℚ`-linear `λ : F → ℚ` (extended to `Λ` along `F → Fₘ`, `exists_proj`). Example
  (`Mixed/NKNonTorsExample`, every check `decide +kernel`): over `θ² = t(t + 27)(t − 48)`,
  `t = log x`, **`∫ θ/(72 x (log x + 24)) dx` is not elementary** (an elliptic integral of the third
  kind; `P = (−24, 72)` has infinite order, certified over `ℚ(i)` at the primes `13` and `193`).
* **Residue divisors at any places** (`Mixed/NKTorsionP`, `Mixed/NKNonTorsP`,
  `nk_not_elementary_P`, `nk_not_elementary_TW`): the same with poles at arbitrary, possibly
  ramified, places above the roots of `D` — the degree argument at infinity along Puiseux roots
  (`order_inf_of_places`), simple poles along `x = α + Tᴺ` (`embG_pole_N`: residue
  `N B(α, y(0))/D′(α)`), `divGE_of_liouville`, and the place certificates of
  `not_torsion_places_map`. These are exactly the certificates of the automatic constant-curve
  pipeline (`emitCurveQ` on `∫ B/D dt`), so non-elementarity proofs over a logarithm are produced
  without hand work. Example (`Mixed/NKRamExample`, certificates from `emitCurveQ` over
  `ℚ[γ]/(γ² + 1296)`, all `decide +kernel`): over `θ² = t(t + 27)(t − 48)`, `t = log x`,
  **`∫ (θ/(72(log x + 24)) + 1/log x) dx/x` is not elementary** (one pole at the ramified place
  `(0, 0)`).
* **Non-Kummer `θ` over an exponential level** (`Mixed/NKExp0`, `Mixed/NKExpLog`,
  `Mixed/NKExpDecide`, `nk_iffE`, `nk_decidesE`): `t = exp(a)`, `θⁿ + ∑ aᵢ(t) θⁱ = 0` with a single
  place above `t = ∞` (`nkShape`) and a single place above `t = 0` (`nkShape0`: `ord₀ a₀ = d₀`,
  `gcd(n, d₀) = 1`, `n ord₀ aᵢ > d₀(n − i)`), `f = ∑ bⱼ(t) θʲ`. Above `0` every branch gives the same
  weighted order (`eval_order_zero`), so a unit of a Liouville form is `c tᵏ` up to an `n`-th power
  (`unit_pow_exp`) and its logarithmic derivative lies in `Fₘ` (`nk_liouvilleE`): `f` is
  elementary iff `f − τ(f)/n` is exact (`exactG` with the exponential solver `expSysT`) and
  `τ(f)/n` is (`elM`). Example (`Mixed/NKExpExamples`): **`∫ (eˣ + e²ˣ)^{1/3} dx` is not
  elementary** (genus `1`). Any basis `w = Tc θ` may be used (`exactT`, `nk_iffET`,
  `nk_decidesET`); with a basis normal at infinity the degree bound holds, and the limit at
  `t = 0` need only be triangular after a permutation (`sys_den_zero_perm`, `zeroOK`). Example: on
  the non-Kummer curve `θ³ + eˣθ = eˣ + e²ˣ`, in the basis `(1, θ²/t, θ)`, **`∫ θ dx` is not
  elementary** and `∫ θ′ = θ` is found. The basis normal at infinity is computed (`nkTc`, `nkTi`:
  `θ^{π r}/t^{⌊π(r) d/n⌋}`, ordered by the fractional weights). The same holds at logarithmic levels
  (`Mixed/NKLogDecideT`, `nk_iffT`, `nk_decidesT`): on `θ³ + (log x)θ = (log x)²` the power basis
  gives `none` while the normal basis proves **`∫ θ dx` not elementary** (`Mixed/NKLogTExamples`).
  At `t = 0` any rational limit with rational eigenvalues is accepted: `zeroOK` tries the
  permutations, then a rational similarity `C Λ₀ C⁻¹` (upper triangular, found by the untrusted
  `triCQ`: characteristic polynomial by Faddeev–LeVerrier, invariant flag by nullspaces; checked;
  `sys_den_zero_sim`). At infinity, `exactTA` (`Mixed/NKExpAuto`, `nk_iffETA`) computes the limit
  matrix, triangularizes it over `ℚ` and retries in the basis `C w` (example
  `Mixed/NKExpAutoExamples`). At finite poles, `exactTS` (`Mixed/NKShear`, `nk_iffTS`, `nk_iffETS`)
  searches the shearings `wᵢ ↦ wᵢ/gᵏ` (the elementary steps of Moser reduction) by the repeated part
  and the linear factors of the matrix denominator: on `θ² + tθ = t³` over `log x` it finds the
  integral basis `(1, θ/t)` from the power basis (`Mixed/NKShearExamples`). `exactTI`
  (`Mixed/NKIntBasis`, decisions `nk_iffTI`, `nk_iffETI`) computes an integral basis normalized at
  infinity (Trager, `autoIntBasis` from Puiseux certificates at the rational singular points;
  untrusted, inverted by Gauss–Jordan and checked by `exactT`): on
  `θ² + (t + 2)θ + 1 + t − t³` the power basis gives `none` and shearing finds nothing (search
  stopped after 25 minutes), while the basis `(1, (θ + 1)/t)` answers (`Mixed/NKIntBasisExamples`).
  Irrational singular points are handled with rational codes (`finIntBasis`): at an irreducible
  factor `p` with `p² ∣ disc`, combinations `∑ cⱼ(t) Bⱼ/(D p)` (`deg cⱼ < deg p`) are made integral
  along the branches at one root of `p` over `ℚ[X]/(p)`; example `(θ + t)² = (t² − 2)²(2t + 3)`
  (basis `(1, (θ + t)/(t² − 2))`, power basis `none`).
  Still `none`:
  irrational eigenvalues, and cases needing non-linear shearing factors or several reduction steps
  beyond the search.
* **Finite poles over an exponential level** (`Mixed/NKExpRes`): residue-free poles
  (`nk_iffRE`, `nk_decidesRE`, certificate `resCert`) and non-zero residues with a logarithm
  certificate (`nk_iffCE`, `logCert`), as at logarithmic levels. Examples
  (`Mixed/NKExpResExamples`): **`∫ (eˣ + e²ˣ)^{1/3}/(eˣ + 1) dx`** and **`∫ (θ + θ′/θ) dx`**
  (`θ³ = eˣ + e²ˣ`) are not elementary.
* **Curves depending on `x`** (`Mixed/NKNonTorsRF`, `nk_not_elementary_RF`): the certificates may
  be over `F = N(x)` (`RatFuncC N`, `N` a number field embedded in the constants), so the curve
  `θⁿ + ∑ aᵢ(x, t) θⁱ` need not be defined over the constants (non-isotrivial curves). The
  realization `psiN : N(x) → L` sends the translated codes `trRF q` to their values
  (`psiN_trRF`); the reductions modulo `p` of `N(x)` send `x` to a transcendental `p`-adic integer
  (`rfFns_exists`). Covered: towers over the line `y = x`, level `0`, constant unramified pole
  points, rational residues. The certificates over `ℚ(i)(x)` are expensive to compute (the global
  certificate of an elliptic curve with degree-`8` coefficients takes about 20 minutes by
  `#eval`); a kernel-checked example is not yet in the build.

* **Two places at infinity** (`Mixed/NKInf2`, `Mixed/NKInf2Log`, `Mixed/NKInf2Decide`): for a
  constant, geometrically irreducible curve `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a logarithmic level with
  two places `P₁, P₂` at infinity, a unit at the finite places has divisor `a(P₁ − P₂)` (degree
  `0`); if `P₁ − P₂` is non-torsion, units are constants, the logarithms of a Liouville form lie in
  the base and the decision is that of a single place (`nk_iff2`, `nk_decides2`: `∫ f` elementary
  iff `f − τ(f)/n` is exact and `∫ τ(f)/n` is elementary). The non-torsion of `P₁ − P₂` is
  certified on the inverted curve `x′ = 1/x`, `y′ = y x′ᵏ` (`mobCurve`), where both places lie
  above `x′ = 0` (`TwoPlaceCertP`: a `PlaceCert` with one fibre and two places, `Γ = (g + m₀e₁)P₁ +
  (m₀e₂ − h)P₂`, checked by `not_torsion_places_map`). The proof (`mem_const_of_unit_two`): the
  unit and its inverse are integral over `C[1/x′]` (`orderTop_nonneg_of_inv_integral`), so they
  have order `0` off `x′ = 0`; the orders above `x′ = 0` sum to `0` (`fibre_sum_zero`, norm
  argument) and are constant on places (`order_rCC_place`, rotations of one Puiseux
  representative); a non-zero order vector is proportional to `Γ − cΓ N`, giving `γ = uᵃ x′^{M cΓ}`
  with `div γ ≥ M Γ − M cΓ ∞′` (contradiction); then `u` is algebraic over `C`
  (`algebraic_of_regularG`) and constant by geometric irreducibility (`mem_const_of_alg_geo`).
  The two charts agree on branches (`embG_mob`). Example (`Mixed/NKInf2Example`): `θ² = t (1 +
  25t)(1 − 2t)(1 − 50t)`, `t = log x` (inverted: `y′² = (x′ + 25)(x′ − 2)(x′ − 50)`, the point
  `(0, 50)` of infinite order; certificates over `ℚ(i)` at `13`, `17`, kernel-checked):
  `not_elementary` proves `∫ θ dx` not elementary, with the `exactC` answer `some false` as a
  hypothesis checked by `#guard` (its kernel evaluation exceeds 30 GB). The same holds over an
  exponential level with a single place above `t = 0` (`Mixed/NKInf2Exp`: `unit_pow_exp2`,
  `nk_liouvilleE2`; `Mixed/NKInf2ExpDecide`: `nk_iffET2`, `nk_decidesET2`); example
  `Mixed/NKInf2ExpExample`: `∫ √(eˣ(1 + 25eˣ)(1 − 2eˣ)(1 − 50eˣ)) dx` is not elementary.
  **A torsion difference** (`Mixed/NKInf2Unit`, `NKInf2UnitLog`, `NKInf2UnitDecide`): given a
  non-constant unit `u₀ = ∑ Uⱼ θʲ` with polynomial inverse (`unitC`), every unit is `c u₀^{b/a}`
  (`mem_pow_unit`: orders along the roots above `x′ = 0` are constant on the two places and sum to
  `0`, so one vanishing order forces all, `fibre_orders_zero_of_one`); the log part is
  `κ u₀′/u₀ + ℓ` (`nk_liouville_unit`), and, when `τ(u₀′/u₀) = 0` (checked), `∫ f` is elementary iff
  `f − τ(f)/n − c u₀′/u₀` is exact for some constant `c` and `∫ τ(f)/n` is elementary (`nk_iff2U`);
  the parametric exactness test is `exactC2` (`exactC2_correct`: the coupled system with the two
  right-hand sides `f, g`). `u₀′/u₀` is certified without gcds (`logDerChk`: `θ′` and `1/P_θ` given,
  unnormalized code arithmetic, so the kernel checks stay cheap). Example
  (`Mixed/NKInf2UnitExample`): `θ² = t² + t`, `u₀ = θ + t + 1/2`: `∫ √(log²x + log x) dx` is not
  elementary (`exactC2` answer by `#guard`). Over an exponential level with a single place above
  `t = 0` (`Mixed/NKInf2UnitExp`: `unit_pow_exp2U`, `nk_liouvilleE2U`;
  `Mixed/NKInf2UnitExpDecide`: `nk_iffET2U`, with the parametric `exactT2` in any basis,
  `Mixed/NKExactW2`, `Mixed/NKExactT2P`); example `Mixed/NKInf2UnitExpExample`:
  **`∫ √(e²ˣ + eˣ) dx` is elementary** (`elementary`; the logarithm is the unit `u₀`).
* **Any number `r` of places at infinity with `r − 1` independent units** (`Mixed/NKInfRDecide`,
  `Mixed/NKInfRLog`, `Mixed/NKInfRUnitExp`, `Mixed/NKInfRExp`): when the `r` places lie in one
  fibre of the inverted curve (`RPlaceDataP`, checked) and units `u₁, …, u_{r−1}` are given
  (`unitsC`: inverses, `uᵢ′/uᵢ` by `logDerChk`, `τ(uᵢ′/uᵢ) = 0`) that are multiplicatively
  independent modulo `Fₘ` (`indepC`: a right inverse of the `(j ≥ 1)`-coordinate minor of the
  `uᵢ′/uᵢ`, unnormalized code arithmetic; `indepC_sound`), every unit is `c ∏ uᵢ^{aᵢ}` up to a
  power (`mem_pow_units`), the log part is `∑ κᵢ uᵢ′/uᵢ + ℓ` (`nk_liouville_units`,
  `nk_liouvilleEU`), and `∫ f` is elementary iff `f − τ(f)/n − ∑ cᵢ uᵢ′/uᵢ` is exact for some
  constants and `∫ τ(f)/n` is elementary (`nk_iffInf` at a logarithmic level, `nk_iffETInf` over an
  exponential level with a single place above `t = 0`). The exactness test with several parameters
  is `exactWL` / `exactTL` (`Mixed/NKExactWL`, `Mixed/NKExactTL`, any solver with a `SolverSpec`);
  the trace check `traceW` uses the `θ′` certificate (the gcd-based `traceC` exceeds 14 GB in the
  kernel for cubics). Examples, for `θ³ + t θ² − t = 0` (`θ = 1/s`, `t = 1/(s³ − s)`, three
  places at infinity, units `1 ∓ θ`): over `t = log x`, **`∫ θ dx` is not elementary**
  (`Mixed/NKInfRExample`); over `t = eˣ`, **`∫ θ dx` is elementary** (`Mixed/NKInfRExpExample`).
  The `exactTL` answers enter as hypotheses checked by `#guard` (too costly for the kernel).
  **Units over a number field** (`Computable/NCodes`, `Mixed/NKUnitN`, `Mixed/NKInf2N`): when the
  places at infinity are Galois-conjugate (e.g. `θ ≈ ±i t`), no non-constant unit has rational
  coefficients. A unit `u = ∑ αᵏ Aₖ` (`α` a root of a monic `μ ∈ ℤ[X]`, codes `Aₖ` over `ℚ`;
  arithmetic in `ℚ(α)` by convolution and reduction modulo `μ` by structural recursion) is
  certified by `unitCN` (`u v ≡ 1`), `logDerChkN` (`u′ = (∑ αᵏ gₖ) u`, `gₖ` over `ℚ`) and `ncC`
  (a coordinate of `∑ αᵏ gₖ` is invertible, so `u ∉ Fₘ`), all valid at every root of `μ`.
  `nk_iff2N`: `∫ f` is elementary iff `f − τ(f)/n − ∑ₖ cₖ gₖ` is exact for some constants and
  `∫ τ(f)/n` is elementary (`⇐`: each `gₖ` is a constant combination of the logarithmic
  derivatives of the conjugate units, by inverting a Vandermonde matrix, `gk_eq_sum`; `⇒`:
  `cₖ = κ αᵏ`). Example (`Mixed/NKInf2NExample`): **`∫ √(1 − log²x)/x dx` is elementary**
  (`elementary`; `u = log x + i√(1 − log²x)`, the arcsine of `log x`). Over an exponential level
  with a single place above `t = 0`: `nk_iffET2N` (`Mixed/NKInf2NExp`); example
  (`Mixed/NKInf2NExpExample`): **`∫ √(eˣ − e²ˣ) dx` is elementary** (`u = 1 − 2eˣ + 2i√(eˣ − e²ˣ)`).
  For `r` places with `r − 1` units over `ℚ(α)` (`Mixed/NKInfRN`: `unitsRNC`, the independence
  certificate `indepCN` — a right inverse over `ℚ(α)` of a minor of the coordinates — and
  `nk_iffRN`, exactness against all components `gᵢₖ`); example (`Mixed/NKInfRNExample`):
  `θ³ − t θ² − t = 0` over `t = log x` has places at infinity `s = 0, ±i` (`θ = 1/s`), rational
  units of rank `1` only, and the independent units `1 ∓ iθ`: **`∫ θ dx` is not elementary**.
  Over an exponential level (`Mixed/NKInfRNExp`, `nk_iffETRN`); example
  (`Mixed/NKInfRNExpExample`): the same curve over `t = eˣ`, **`∫ θ dx` is elementary**
  (`θ dx = d(1/s − 2 arctan s)`).
  **The units are found automatically** (`Mixed/NKUnitFind`, untrusted, every output re-checked
  by the theorems' checks): a unit with divisor `∑ c_π P_π` supported at infinity is a non-zero
  solution of the linear conditions `ord_π u ≥ c_π` along the Puiseux branches of the inverted
  curve (degree `0` forces the exact divisor and no finite zero); `autoInfUnits` produces the
  units `P_i − P_{r−1}` and their inverses over `ℚ(α)`, the components of their logarithmic
  derivatives, the independence certificate (Gauss–Jordan over `ℚ(α)(x, t)`), the trace codes and
  the place certificate. Examples (`Mixed/NKUnitFindExamples`): all the certificates of the
  three-place curves `θ³ ∓ t θ² − t` (over `ℚ` and `ℚ(i)`) are regenerated and pass the checks.
  Not covered: the search is bounded (multiples and degrees), so it is a practical procedure, not
  proved to find units whenever they exist (they are certificates; in genus `0` they always exist), the case where the
  classes of the places at infinity have rank `< r − 1` with no units supplied (Mordell–Weil
  relations), non-constant (`x`-dependent) curves.

Not done yet: for supplied bases (`exactT`), matrices whose limits at `t = 0` or at infinity are
not rational triangular (non-rational or non-triangularizable in the given basis, or `Λ₀` with
positive integer diagonal entries) — for constant curves the search `searchTRE` avoids this
(`nk_decidesTRE`); and multiple factors `p²∣q` of the matrix denominator where the leading
matrix is singular mod `p` (then the indicial norm vanishes identically; this needs Moser
reduction, or a better basis: `exactT` with an integral basis supplied). Multiple factors with an
invertible leading matrix are handled: `sys_den_pole` then
gives `p ∣ det A₀`, a contradiction, so the pole order is that of the right-hand side (checked:
`Y′ + Y/t² = 1/x + 1/t` over `t = log x` returns the solution `Y = t`) (these need
systems one level down or Moser/Barkatou reduction; the solvers answer `none`); the log part for
non-Kummer `θ` with several places at infinity without a full set of supplied units, or over exponential levels beyond single places
above `0` and `∞` (`nk_iffE`, `nk_iffRE`, `nk_iffCE`); with finite poles
of non-zero residue, only the two sides with certificates are done (a logarithm certificate:
`nk_iffC`; a non-torsion certificate for a curve over `ℚ` with unramified `F`-rational poles:
`nk_not_elementary`, at any places: `nk_not_elementary_P`); poles at
points not rational over a computable `F`, and the completeness of the torsion test (a curve over
a function field: specialization) are open. Examples (`Mixed/SysPrimExamples`, `#guard`, seconds each): `Y′ = 1`,
`Y′ + Y/(x log x) = 2/x` (solution `log x`, homogeneous `1/log x`), and the coupled system
`Y₁′ + Y₂/(x log x) = 1/x`, `Y₂′ = 1/x` (solution `(0, log x)`).

## Not done

The full Risch–Trager–Bronstein algorithm is **not** complete. The main remaining gaps, and what
each needs:

* **Algebraic extensions over transcendental levels, in general.** Decided: an arbitrary curve
  over `ℚ` at the base with any tower of logarithms and exponentials on top (`elM_decides_any`,
  any constants), algebraic functions of a single logarithm or exponential by a change of the
  base variable (`elM_decides_rescaled`), and Kummer radicals `B(t) a(t)^{j/n}` over a logarithmic
  level (`kp_decides`, `kp_decides_pow`: `∫ B(t) a(t)^{j/n − k}`, e.g. `√(x + log x)`,
  `1/√(x + log x)`), and sums `g₀ + ∑ⱼ Bⱼ a^{j/n − kⱼ}` of these (`kl_decides`). Integrands with poles at ordinary places are decided for square roots
  over a logarithmic level with linear pole factors `t − c_q` and residues in any number of
  classes `ℚ√s` (`kqmDecide_correct`; with local torsion certificates it always answers for
  suitable residues and large bounds, `kqm_decided`).
  The same holds over an exponential level (`kxDecide_correct`, poles at `c_q ≠ 0` and a power
  of `t` in the denominator; `kx_decided`), except when a class and `P₊ − ∞` are both
  non-torsion (a Mordell–Weil relation question, answered `none`).
  Radicals of any order `n` over an exponential level are decided for integrands
  `B(t) θʲ/(tᵏ Aˡ)` (`krDecide_correct`; `kr_decided`: it always answers for suitable residues).
  With ordinary poles `t = c_q ≠ 0` they are decided as well (`kyDecide_correct`, with a number
  field containing the residues supplied and checked), except for the Mordell–Weil case below.
  Radicals of any order `n` over a **logarithmic** level with ordinary poles `t = c_q`
  (`B(t) θʲ/(∏(t − c_q) Aˡ)`, `θⁿ = A(t)`) are decided by `kvDecide` (`Mixed/KV*`,
  **`kvDecide_correct`**, number field supplied and checked as for `kyDecide`); over a logarithm
  there is a single place at infinity and no special fibre, so there is no Mordell–Weil exception
  (a non-torsion component means not elementary, `kv_forward_neg`; units without finite zeros or
  poles are constants, `kv_liouville`). With the antiderivative: `kvDecideCW`,
  `kvDecideCW_isSome`, `kvDecideCW_valid`. Example (`Mixed/KVExamples`): `∫ ∛(log x)/(x(log x − 1))`
  elementary (about 3 min), `∫ ∛(log x)/(log x − 1)` not.
  Pole factors of degree `> 1` whose roots lie in `Fₘ ⊗ N` for a number field `N` are decided too
  (`kzDecide_correct`, e.g. `e²ˣ + 1`, whose roots `±i` are constants).
  Pole factors, at any level, whose roots are algebraic over the base field `F₀` (e.g. `t² − x`)
  are decided after a change of base curve certified by an Eisenstein criterion or by a single
  place at infinity (`kzDecide_bc_correct`, `geomIrr_of_wt`).
  Not treated:
  * pole factors whose roots are algebraic over a transcendental level but not over `F₀` (e.g.
    `t₁² − x − t₀`), which needs the non-Kummer machinery;
  * (resolved) new base curves that are neither Eisenstein nor have a single place above some rational point
    or infinity (a single place at infinity is certified by the weights: `geomIrr_of_wt`,
    `Mixed/KBWeights`, example base `w² + x w = x³ + 1`; a single place above a rational point
    `x = a` by the weights of the inverted curve `x′ = 1/(x − a)`: `geomIrr_of_wt_mob`,
    `Mixed/GeomIrrMob`, from `irreducible_of_mob` — irreducibility transfers back through the
    inversion — example `Y³ = x²(x − 1)²(x − 2)²` in `Mixed/GeomIrrMobExamples`). In general,
    **`geomIrr_of_subsets`** (`Mixed/GeomIrrMob`) certifies geometric irreducibility of any
    geometrically irreducible curve: the subset certificate `irrSubsetCheck` at a split point, with
    branches over a number field, proves irreducibility over every extension of that field, hence
    over the algebraic closure of any `K ⊇ ℚ`, hence over `K` (example `Y⁴ − (x² + 3)Y² + x²` at
    `x = 1` over `ℚ(√2, √3)`, `Mixed/GeomIrrSubExamples`, kernel-checked); any such certificate
    feeds the base-change decision (`fKc_irr_geom`, `qK_irr_linear_geom` give the irreducibility
    facts `kzDecide_bc_correct` needs). So new base curves are no longer restricted;
  * non-Kummer `θ` (`θⁿ + ∑ aᵢ(t) θⁱ = 0`, integrands polynomial in `t` and `θ`) is decided —
  with an explicit antiderivative (`nk_integrate*`) — over a logarithm with one place at infinity
  (`nk_decidesTV`; constant coefficients `nk_decidesTR`), several rational places at infinity,
  split (`nk_decidesInfVGPW`) or of one slope `s/e` (`nk_decidesInfVRPW`); over an exponential
  with single places above `0` and `∞` (`nk_decidesTEV`, `nk_decidesTRE`), several places at
  infinity (`nk_decidesETInfVGPW`, `nk_decidesETInfVRPW`) and also several places above `0`
  (`nk_decidesETInf0PW`, `nk_decidesETInf0RPW`). With several places these decisions assume that
  enough S-units exist (`r − 1` for `r` places, multiplicatively independent: `nk_decides…PM`); they
  exist exactly when the divisor classes of the places at infinity (and above `0`) are torsion,
  and when they do not the search does not answer — the Mordell–Weil question below, over the
  function field `Fₘ`. **Several slopes at infinity** are decided at a logarithmic level when the
  places at infinity are unramified and rational (`nk_decidesInfVM`, `nk_decidesInfVMP`,
  `Mixed/NKDecidesInfVM`): the code check `multiShapeC` gives the Newton segments with their residual
  polynomials; the initial forms of `∏(X − r)` over Laurent series (`NKInitForm`, `NKMultiRoots`,
  `NKMultiData`: no Newton-polygon theory needed) give the orders and leading coefficients of the
  roots above infinity; Galois descent on Laurent series (`NKGalRoots`: automorphisms of `K/Fₘ` act
  coefficientwise and permute the roots; a root with unique data is fixed) makes the values of the
  rescaled basis along the roots rational, and the rotation `T ↦ ζT` plus the transfer between branch
  systems (`infOrd_of_sys`) make them invertible (`multi_gauge`), hence `exactTLVG_exists_multi`.
  Example (`Mixed/NKMultiExamples`): `θ² − (log x) θ + x log x = 0`, slopes `1` and `0`: `∫ θ dx` is
  not elementary (40 s). **Ramified segments** too (`nk_decidesInfVMR`, `Mixed/NKDecidesInfVMR`):
  `multiShapeRC` checks segments of rational slopes `sₖ/eₖ` with residual polynomials
  `c Z^{lo} ∏ (Z^{eₖ} − γ)`; `multi_hdataR` gives orders `−(N/eₖ) sₖ` and `lcᵉ = γ`; the roots of a
  place are rotations of a representative (`orbit_data`, `rot_of_pow_eq`), the window jets twisted
  by a power of the leading coefficient are rational by a Galois eigenvector argument
  (`jet_eigen`), and the gauge is invertible with diagonal `(t/e) γ′/γ` (`multi_gauge_ram`); the
  limit system is then non-degenerate because the gauged system is diagonal
  (`exactTLVG_exists_multiR`), and `∑ₖ |Γₖ| − 1` independent units span the units
  (`unitsSpan_multiR`). Example (`Mixed/NKMultiRExamples`): `θ³ − (log x) θ + x log x = 0`, slopes
  `1/2` (ramified) and `0`: `∫ θ dx` is not elementary (~3 min). **At an exponential level**
  (`nk_decidesETInfVMR`, `Mixed/NKDecidesETInfVMR`, a single place above `t = 0`): the window jets
  pick up `−(h/e) a′` (`multi_gauge_ramE`), so the gauged limit is diagonal with data
  `(−h/e, t/e, γ)` (`exactTLEVG_exists_multiR`); example (`Mixed/NKMultiRExpExamples`):
  `θ³ − eˣ θ + x eˣ = 0`: `∫ θ dx` is not elementary (~1 min). With several places above `t = 0`
  too (split fibre, `split0C`): `nk_decidesETInf0MR` (`Mixed/NKDecidesETInf0MR`; gauge at `0` of
  `exists_gauge0_split`, `exactTLEVG_exists_multiR0`; `∑ₖ |Γₖ| + n − 2` S-units with `x` span the
  S-units, `unitsSpan0_multiR`; variants `…P`, `…PW`, `…PM` and the antiderivative
  `nk_integrateETInf0MRPW` in `Mixed/NKMultiR0Wit`). Variants: `…PW` (no independence
  certificate), `…PM` (multiplicatively independent units), and the antiderivative
  `nk_integrateInfVMRPW`, `nk_integrateETInfVMRPW` (`Mixed/NKMultiRWit`). **Residue-free finite
  poles** with several slopes (`nk_decidesInfVMRR`, `nk_decidesETInfVMRR`, `Mixed/NKDecidesInfVMRR`,
  `NKDecidesETInfVMRR`): integrands `∑ bⱼ(t)/D(t) θʲ`, `D` squarefree, with the certificate
  `resCert` (`Bᵏ ≡ U D mod P`, so `f dx` has no pole above the roots of `D`); the logarithms of a
  Liouville form are still units (`nk_liouville_units_spanR`, via `logs_zero_branchR`). Example
  (`Mixed/NKMultiRRExamples`): on `θ³ − (log x) θ + x log x = 0`, `∫ θ/log x dx` is not elementary
  (`θ³ = t(θ − x)`), and `∫ (θ/t)′` is found; with the antiderivative and without certificates:
  `nk_integrateInfVMRRPW`, `nk_integrateETInfVMRRPW`, `…RRPW`, `…RRPM` (`Mixed/NKMultiRRWit`).
  **Non-zero residues** with a logarithm certificate (`nk_decidesInfVMRC`, `nk_decidesETInfVMRC`,
  `Mixed/NKMultiRC`): for any `f = ∑ fⱼ θʲ` and `(uⱼ, cⱼ)` (`logCert`, `cⱼ ∈ ℚ`) with
  `f − ∑ cⱼ uⱼ′/uⱼ` residue-free, the decision of the residue-free part decides `f` (example:
  `∫ (θ′/θ + θ/log x) dx` not elementary); the certificate exists exactly when the residue
  divisors are torsion (with rational residues), the same question as for the units.
  Places at infinity whose residue fields are generated by elements algebraic over `F₀` are
  handled by changing the base curve (`nk_decidesInfVMR_bc`, `nk_decidesETInfVMR_bc`,
  `Mixed/NKBCMR`, via `bc_decides`). Not covered: places at
  infinity or above `0`
  whose residue field is not generated over `Fₘ` by elements algebraic over `F₀` (Risch equations
  over algebraic extensions of a transcendental level), finite poles with non-zero residues for
  non-constant curves (for constant curves:
  residue-free poles `nk_iffR`, certified residue divisors `nk_iffC`, `nk_not_elementary`, and
  units over `ℚ(α)` supplied, `nk_decidesRNTR`, `nk_decidesETRNTRE`). Towers
  whose data are algebraically dependent (`exp(x/2)` over `exp x`) fail the certificate `certC`
  and must be rewritten with independent generators (`exp(x/2)` alone).

* **General algebraic integrands, practical side** (arbitrary curves `F(x, y) = 0`, `Curves/`,
  `Torsion/`). Decidability is proved (`decideTotal_decides`, see *General algebraic curves*):
  for every large bound the exhaustive enumeration answers and the answer is correct. What is
  not done is a *practical* complete procedure: the fast pipeline (`decideCurveQ`, `decideLogTP`)
  is sound, but its completeness (`≠ none`) is not proved, the splitting field for non-split
  residue points must be supplied to it, and its witness search is heuristic (`decideAuto`).
* **Mordell–Weil relations.** `kxDecide` answers `none` when a residue class and `P₊ − ∞` are
  both non-torsion. The non-elementary direction is now stated with the exact condition
  (`Mixed/KXNoRel`, **`kxe_norel`**): if for a class `k₀` with a non-zero residue no function has
  divisor `N Δ_{k₀} + μ δ₀` (`N > 0`, `μ ∈ ℤ`, `δ₀ = P₊ − P₋`), there is no Liouville form — a
  two-point independence statement. The bridge from these `ordAt`-divisors to Mathlib's points is
  proved for `y² = x³ + ax + b` over an algebraically closed field (Abel's theorem, the needed
  direction: `Mixed/AbelSum.abel_sum` — a function with affine divisor `∑ nᵢ (Pᵢ)` forces
  `∑ nᵢ Pᵢ = 0`; from `Algebraic/AbelLine` (orders of lines, branch and non-branch),
  `Mixed/AbelLine2` (the line's divisor `(P) + (Q) + (−(P+Q))` via Mathlib's `addPolynomial_slope`),
  `Algebraic/AbelPole` (no function with divisor `(R) − ∞`)), and for any cubic
  `y² = c₃x³ + c₂x² + c₁x + c₀` through Mathlib's model `Y² = X³ + c₂X² + c₁c₃X + c₀c₃²`
  (`Mixed/AbelGen.abel_sumG`). With it, **`Mixed/KXAbel.kxe_norel_group`**: on `θ² = c₃t³ + …`, if
  `2N ∑ m_q P_q + 2μ P₊ ≠ 0` in Mathlib's group for all `N > 0, μ` (points of the model
  `Y² = X³ + c₂X² + c₁c₃X + c₀c₃²`), then there is no Liouville form (`hnorel_of_group` reads the
  divisor `N Δ_{k₀} + μ δ₀` as a point sum on the base change). The group condition reduces to a
  height certificate: the exception's points lie over the coefficient field `C` (`hgrp_of_C`), and
  for `C ≃ k(X)` (the base `ℚ(x)`, or `Kₘ = Kₘ₋₁(tₘ₋₁)`) Mathlib's model embeds injectively into a
  polynomial short curve over `k(X)` (`Mixed/KXHeight`: `toShort`), so an `ell_indep` certificate
  gives the hypothesis (`hgrp_of_height`). The certificate is executable and proved
  (`Mixed/EllCompute`, `EllCompute2`: heights of reduced pairs via the executable gcd, the group law
  on executable fractions `addC_spec`, `certQ`, `indep_of_certQ`); **kernel-checked example**
  (`Mixed/EllCertExample.indep_example`): on `y² = x³ − x + t²` over `ℚ(t)`, `(0, t)` and `(1, t)`
  are independent (heights of `8P, 8Q, 8(P+Q)` all `42`, certificate at level `3`, `decide
  +kernel` in about 2 min). **The forward direction at the level of the decider's data**
  (`Mixed/KXForwardMW.kx_forward_mw`): in the exception (`√A(0) ∈ Fₘ`, a class and `P₊ − ∞` both
  non-torsion) with `deg A = 3`, the group condition for one reference choice of the square roots
  (in the algebraic closure of `Fₘ`) excludes every Liouville form — the proof's roots differ by one
  sign per class (`KXRootSign.prodRoots_sign`) and the condition is sign-invariant (`grp_signs`);
  points of the model are nonsingular (`AbelGen.ns_of_eq`). At the level of `kxDecide`'s statement
  (`Mixed/KXNotElemMW.kx_not_elementary_mw`): in the exception with `deg A = 3`, if in every
  realization of the tower the group condition holds for some choice of the square roots, the integral
  is **not elementary**; `kx_not_elementary_mwC` states the hypothesis over `Fₘ` itself (any roots in
  `Fₘ`, transferred to the closure by `hgrp_of_C`). The code-level certificate: level-0 codes as
  executable fractions (`Mixed/CodeFr`), `T.F 0 ≃ Cc(X)` on a linear base (`Mixed/KXField.phi0_sem`),
  extension of constants (`Mixed/EllBaseChange.indep_mapE_of_certQ`), and **one Boolean check**
  (`Mixed/KXCertBridge.kxChk`: denominators, `B(c_q) ≠ 0`, the short model `Ac, Bc` and its
  discriminant, `z²A(0) = r²`, and `certQ` on the executable points `∑ m_q P_q` and `P₊ = (0, r/z)`)
  that proves the hypothesis in every realization and for every choice of `√A(0)`
  (**`grp_of_chk`**; level `0`, linear base, all squared residues rational squares,
  `kxGens = []`). **End-to-end example** (`Mixed/KXMWExample.not_elementary_mw`):
  `∫ √(e³ˣ − eˣ + x²) / (x (eˣ − 1)) dx` is **not elementary** — `kxDecide` answers `none` there
  (`P = (1, x)` and `P₊ = (0, x)` both non-torsion), and the kernel-checked certificate decides the
  Mordell–Weil question (all checks `decide +kernel`, about 2 min, 15 GB). **Automatic search**
  (`Mixed/KXMWDecide.kxDecideMW0`, correct by **`kxDecideMW0_correct`**): `kxDecide` at level `0`,
  and when it does not answer, the bridge data is computed (`z` from `kxZ`, `r = Rat.sqrt κ`, `u` the
  product of the coefficient denominators, `Ac`, `Bc` from the normalized fractions, every class and
  level `≤ kmax`) and a passing `kxChk` answers `some false`. The certificate uses
  `D/gcd(m_q)` (the group condition for `D′` implies it for `g D′`), which keeps heights small:
  `√(e³ˣ − eˣ + 4x²)/(x (eˣ − 1))` (residue `2`) is decided in seconds. **Irrational square roots**
  (`Mixed/KXCertBridgeK`): the certificate over a field `k₀ ⊇ ℚ` containing roots `ρᵢ` of the class
  generators and `σ` of `κ` (`kxChkK`, points `(x_q, y_q · c_q∏ρᵢ)`, `P₊ = (x₀, (u³c₃/z) σ)`);
  the realization's roots are constants (`const_of_sq`: a square root of a non-zero rational has
  zero derivative), so an embedding `j : k₀ → Cc` (`hlift`; for `ℚ(√d)` = Mathlib's computable
  `QuadraticAlgebra ℚ d 0`: `Mixed/KXQuadLift.qa_lift` via `qaEmbed`) transports the certificate
  (**`grp_of_chkK`**). Decider: `Mixed/KXMWDecideQ.kxDecideMWQ0` (rational search, then `ℚ(√d)` for
  `kxGens = [d]` or `κ` not a square; correct by **`kxDecideMWQ0_correct`**). Example theorem
  (`Mixed/KXMWExample2.not_elementary_mw2`): **`∫ √(e³ˣ − eˣ + 2x²)/(x (eˣ − 1)) dx` is not
  elementary** (residue class `ℚ√2`, `κ = 2`). **Twist** (`Mixed/KXCertBridgeT`, cheaper and for any
  number of generators): `D` only involves the poles of one class `T`, whose ordinates are rational
  multiples of `r = ∏_T rᵢ` (`r² = s = ∏_T gᵢ`); when `κ = s c²`, scaling the model by `u = u₀ r`
  makes all coordinates rational, so the certificate `kxChkT` is over `ℚ` (**`grp_of_chkT`**;
  decider `Mixed/KXMWDecideT.kxDecideMWT0`, correct by **`kxDecideMWT0_correct`**). The `√2` example
  is proved this way (kernel check about 95 s, 16 GB; the direct certificate over `ℚ(√2)` needs
  about 34 GB). **Conjugation** (`Mixed/KXConj`, `Mixed/KXCertBridgeC`): when `D` and `P₊` are in
  different classes (`δ = s κ` not a square), over `ℚ(√δ)(x)` the conjugation fixes `D` (rational on
  the twist) and negates `P₊`, so `2N D + 2μ P₊ = 0` forces `4N D = 0` (**`FFHeight.conj_nontors`**);
  a one-point certificate `ĥ(D) > 0` over `ℚ` (`certQ1`, **`nontors_of_certQ1`**) suffices
  (**`grp_of_chkC`**). Decider `kxDecideMWC0` (rational, twist, conjugation, `ℚ(√d)`; correct by
  **`kxDecideMWC0_correct`**): at level `0` over a linear base every square-class configuration of
  the exception is now handled by a certificate over `ℚ` — same class by the twist, different
  classes by conjugation. Example (`Mixed/KXMWExample3.not_elementary_mw3`):
  **`∫ √(e³ˣ − (x²+1)eˣ + 2x²)/(x (eˣ − 1)) dx` is not elementary** (`P = (1, x)`, `P₊ = (0, √2 x)`;
  kernel check 19 s). **Constant curves** (`Mixed/QHeight`, `Mixed/KXCertBridgeCK`): heights over
  `k(x)` vanish on constant points, so the logarithmic height over `ℚ` on `y² = x³ + ax + b`
  (`a, b ∈ ℤ`) is formalized: the duplication bound **`QHeight.hP_double`**
  (`|h(2P) − 4h(P)| ≤ log C(a,b)`, via the resultant identities over `ℤ` and an evaluator for
  coefficient bounds), torsion points have canonical height `0` (`canon_torsion`, bounded orbit), and
  the executable certificate `certH` (`H(x(2ᵏP))³ > C`, integer comparison only) proves infinite
  order (**`nontors_of_certH`**); the embedding `E(ℚ) → E(ℚ(x))` (`ιQ`) carries it into the
  conjugation argument (`grp_of_chkC0`, now parametrized by the non-torsion input):
  **`grp_of_chkCK`**, decider `Mixed/KXMWDecideK.kxDecideMWK0` (correct by
  **`kxDecideMWK0_correct`**). Example (`Mixed/KXMWExample4.not_elementary_mw4`):
  **`∫ √(1 + eˣ + e³ˣ)/(eˣ − 1) dx` is not elementary** — the `none` case of `KXExamples`
  (`D′ = (3, 9)` on `y² = x³ + 9x + 27`; kernel check 12 s). **Same class, constant curves**
  (`Mixed/QPar`): the parallelogram bound over `ℚ` (**`QHeight.hP_par`**: Gauss's lemma over `ℤ`
  `dvd_of_primZ`, `max(|q₃q₄|,|q₃p₄+p₃q₄|,|p₃p₄|) ≥ H₃H₄/2`, the quadratic of `x(P±Q)`, the lower
  bound from the upper one and duplication), the canonical pairing over `ℚ`, and the two-point
  certificate `certG` (bit lengths of `H(x(2ᵏP))`, `H(x(2ᵏQ))`, `H(x(2ᵏ(P+Q)))`; the Gram inequality
  is homogeneous, so it is checked over `ℚ` in units of `log 2`) proving independence
  (**`indepQ_of_certG`**). The twisted bridge is parametrized by the independence input
  (`grp_of_chkT0`); **`grp_of_chkTK`**; `kxDecideMWK0` now also searches this branch. Example
  (`Mixed/KXMWExample5.not_elementary_mw5`): **`∫ √(e³ˣ − eˣ + 4)/(eˣ − 1) dx` is not elementary**
  (`(1, 2)`, `(0, 2)` independent on `y² = x³ − x + 4`; kernel check 30 s). At level `0` over a
  linear base the exception is now certified whenever the points are independent. **Dependent
  classes** (`Mixed/KXDep`, `Mixed/KXDepCodes`, `Mixed/KXForwardDep`, `Mixed/KXDepMain`): when a
  non-torsion class satisfies a relation `N Δ_k ± M δ₀ ∼ 0` (only possible when `s_T κ = r²`, and
  then `P₊ = (0, ±r/z)` on the twist `ỹ² = s_T A` over `Kₘ`), a witness `W` of `N Γ_k + M P_±`
  gives the generator `W² ∏(t − c_q)^{−N m_q} t^{−M}` of divisor `N Δ_k ± M δ₀` (`ordAt_zD`); since
  no multiple of `δ₀` is principal, the divisor of every logarithm lies in the span of the
  generators, so a Liouville form forces the parametric equation with one column per class
  (**`kxe_dep`**; the class witnesses read on `y² = A` by `class_witness` on the augmented point
  set, `gammaQ_aug`, **`kx_class_witsD`**, **`kx_forward_dep`**). `kxDecideD` runs `kxDecide`, then
  searches `1 ≤ N, M ≤ nmax` and both signs for a witness (`kxDepSearch`, the point checked on the
  twist) and solves the parametric equation; backward by `kx_backward` (any witness gives an
  elementary column). Correct by **`kxDecideD_correct`** (any level `m`, any base curve). Examples
  (`Mixed/KXDepExamples`, `#guard`): `∫ √(e³ˣ − eˣ + 1)/(eˣ − 1)` is **not elementary**, and
  `∫ (e²ˣ + 3eˣ − 1) √(e³ˣ − eˣ + 1) / (2 (eˣ − 1)(e³ˣ − eˣ + 1))` is **elementary** — both `none`
  for `kxDecide` and outside the independence certificates. **The search is complete** (linear base;
  `Mixed/KXDepConj`, `Mixed/KXDepFind`, `Mixed/KXDepDecides`): a relation with `δ₀` forces `P₊` to be
  defined over the code field on the twist — otherwise `F(√δ)` has two embeddings `√δ ↦ ±μσ`, the
  relation descends (`principalMulN_descend`) and its conjugate gives the relation at `(0, −σ)`,
  whose quotient is a principal multiple of `δ₀` (**`rel_point_defined`**); with
  `ordAt_unzD` (the converse of `ordAt_zD`) and `kxe_norel`, a Liouville form makes every
  non-torsion class pass the search (**`kx_rel_found`**). Hence **`kxDecideDL_decided`**: for
  accepted data over a linear base, at suitable residues and every large bound there is `N₀` with,
  for every `nmax ≥ N₀`, either a correct answer of `kxDecideDL` or **the integral is not
  elementary**. The remaining `none` answers are exactly non-elementary integrals with a class
  independent of `P₊ − ∞`; turning those into answers needs the existence of the independence
  certificates. **Over `ℚ` they exist** (`Mixed/QHeightExists`, `Mixed/MWPairPos`,
  `Mixed/QIndepExists`): Northcott over `ℚ` (`finite_Hq_le`, `finite_hP_le`), so a point of infinite
  order passes `certH` at some level (**`certH_exists`**); the canonical height is `≥ 0`, vanishes only
  on torsion (`torsion_of_canonQ_zero`), and the Gram determinant of independent points is positive
  (**`MWPair.gram_pos_of_finite`**: a semidefinite binary form would have lattice vectors of
  arbitrarily small positive value by Dirichlet's approximation theorem, infinitely many of them of
  bounded height; **`gramQ_pos`**), so independent points pass `certG` at some level
  (**`certG_exists`**). Towards a decision theorem for constant curves: the constant-curve search
  now also tries the common denominator of the model (`mwScales`), so an integral model is always
  among the candidates; a realization with the square roots exists without an antiderivative
  (`Mixed/KQRoots.kq_roots`); the converses of the bridge checks (`Mixed/KXCertBridgeTRev`:
  **`indep_of_grpT0`**, **`indep_of_grpC0`** — independence on the curve makes the certificate points
  independent/non-torsion); the constructive direction of Abel's theorem
  (`Mixed/KXAbelRev.pm_of_group`: a group relation `2N D + 2μ P₊ = 0` gives `PrincipalMulN` over
  `Fₘ`, via `exists_hG` on the base change and `principalMulN_descend`); and the relation search from
  `PrincipalMulN` (`kx_rel_found_of_pm`, `rel_point_defined_pm`, `principalMulN_restrict`). The
  structural parts pass on valid data (`Mixed/KXConstComplete`: **`kxChkC0_true`**,
  **`kxChkT0_true`** — well-formed codes, constant coefficients, nonzero discriminant; constant
  elliptic curves have no non-constant points, `Mixed/EllConstPts.weierstrass_const`), so the checks
  pass at some height level (`Mixed/KXConstCK`: **`kxChkCK_exists`**, **`kxChkTK_exists`**) and the
  searches succeed at the integral scaling (`Mixed/KXConstSearch`: **`kxMWSearchCK_of`**,
  **`kxMWSearchTK_of`**). **Assembly** (`Mixed/KXDepOrIndep`, `Mixed/KXConstAssembly`): in a
  realization with the constant square roots (`lift_sqrts`, no antiderivative needed), a class
  certified non-torsion is either dependent on `P₊` — then the relation search finds the relation
  (**`kx_dep_or_indep`**, via `pm_of_groupC`) — or independent, with `P₊` and the class point of
  infinite order (the oracles' certificates, `isPrincipalS_class_of_pm`, `isPrincipalS_P0_of_pm`).
  Decider `kxDecideDK0` (`kxDecideDL`, then the constant-curve searches; correct by
  **`kxDecideDK0_correct`**) and **`kxDecideDK0_decides`**: for a cubic with rational coefficients
  over a linear base (well-formed codes), at suitable residues, for every large bound, relation bound
  and height level, `kxDecideDK0` **answers** (correctly) — the Mordell–Weil exception is decided for
  constant curves. For non-constant curves over `K(X)` the analogous positivity is now proved
  (`ExH.hint_htor`, `Mixed/ExH*.lean`, see below).
  **Levels `m + 1`** (`Mixed/MTField`, `Mixed/KXCertBridgeS`, `Mixed/KXMWDecideS`): for any base
  curve, `F(m+1) = Fₘ(tₘ) ≃ Fₘ(X)` (`phiS`), codes of level `m + 1` translate to executable
  fractions over the computable field `Kₘ` (`trFr`, **`phiS_val`**), and the twisted bridge
  transfers (**`grp_of_chkT0S`**, **`grp_of_chkTS`**, certificate over `Kₘ`); decider
  `kxDecideMWS` (correct by **`kxDecideMWS_correct`**). Example (`Mixed/KXMWExamplesL1`, `#guard`):
  `∫ √(e^{3eˣ} − e^{eˣ} + e^{2x})/(e^{eˣ} − 1) dx` (tower `x, eˣ, e^{eˣ}`) — `kxDecide` answers
  `none`, `kxDecideMWS` answers **not elementary** (evaluation about 2 min). **Conjugation at levels
  `m + 1`** (`Mixed/KFSquare`, `Mixed/KXCertBridgeCS`): for a linear base a rational non-square stays
  a non-square in every `Kₘ` (**`not_isSquare_KF`**: square roots of constants in `K(X)` lie in `K`,
  and `K₀ ↪ ℚ(x)`), so `Kₘ(√δ)` is a field (Mathlib's `QuadraticAlgebra`), and the conjugation
  argument transfers (**`grp_of_chkC0S`**, **`grp_of_chkCS`**; `cert_ptψG`/`cert_sumψG` over any base
  field); `kxDecideMWS` searches this branch too. Example (`#guard`):
  `∫ √(e^{3eˣ} − (e^{2x}+1)e^{eˣ} + 2e^{2x})/(e^{eˣ} − 1) dx` is not elementary (4 min evaluation).
  **Rational-coefficient curves at levels `m + 1`** (`Mixed/EllConstK`, `Mixed/KXCertBridgeCKS`,
  `Mixed/KXMWDecideSK`): `E(ℚ) ↪ E(K(X))` for any `K` of characteristic `0` (`ιQK`,
  `nontors_constK`, `indep_constK`); the coordinates of `D′`, `P₊′` are verified rational in `Kₘ`
  (`ratOfK`, `ptRat`) and certified by heights over `ℚ` (`kxChkCKS`, `kxChkTKS`, soundness
  **`grp_of_chkCKS`**, **`grp_of_chkTKS`**); decider `kxDecideMWSK` (correct by
  **`kxDecideMWSK_correct`**). Examples (`Mixed/KXMWExamplesL1K`, `#guard`, ~4 min):
  `∫ eˣ √(e^{3eˣ} + e^{eˣ} + 1)/(e^{eˣ} − 1) dx` and `∫ eˣ √(e^{3eˣ} − e^{eˣ} + 4)/(e^{eˣ} − 1) dx`
  — `kxDecide` and `kxDecideMWS` answer `none`, `kxDecideMWSK` answers **not elementary**.
  **Kernel-checked at level `1`** (`Mixed/KXMWExampleL1KK`, ~30 s): all side checks, the tower
  certificate `certC 2` and the height certificate (`kxChkCKS`, `D′ = (3, 9)` on
  `y² = x³ + 9x + 27`) by `decide +kernel`, giving the theorem **`not_elementary_L1K`**:
  `∫ eˣ √(1 + e^{eˣ} + e^{3eˣ}) / (e^{eˣ} − 1) dx` is not elementary (standard axioms only).
  **Completeness at levels `m + 1`** (`Mixed/KXCertBridgeSRev`, `Mixed/KFConstPts`,
  `Mixed/KFRatGuess`, `Mixed/KFConstTail`, `Mixed/CodeWFS`, `Mixed/KXConstCompleteS`,
  `Mixed/KXConstSearchS`, `Mixed/KXConstAssemblyS`): the converse bridges (`indep_of_grpT0S`,
  `indep_of_grpC0S`); points of `y² = x³ + ax + b` (`a, b ∈ ℚ`) over every `Kₘ(X)` have rational
  coordinates (`KF_point_rat`, `rat_point_KF`: constant points over `Kₘ₊₁ = Kₘ(t)`, down to
  `K₀ ↪ ℚ(x)`, with rational squares descending); `ratGuess` is exact on rational constants;
  well-formedness of level-`m + 1` codes (`pres_monomial`, `okS_kxD`, `okS_normC`); the structural
  checks pass (`kxChkC0S_true`, `kxChkT0S_true`), the checks pass at some height level
  (`kxChkCKS_exists`, `kxChkTKS_exists`), the searches succeed (`kxMWSearchCKS_of`,
  `kxMWSearchTKS_of`; the searches now use rational scalings, since `mwUS` can be irrational in
  `Kₘ`). Decider `kxDecideDKS` (`kxDecideDL` at level `m + 1`, then these searches; correct by
  **`kxDecideDKS_correct`**) and **`kxDecideDKS_decides`**: for a cubic with rational coefficients
  over a linear base (well-formed codes), at every level `m + 1`, `kxDecideDKS` answers for all large
  bounds — the Mordell–Weil exception is decided for rational-coefficient curves at every level.
  **Antiderivatives** (`Mixed/KXDepWit`): the dependent case is constructive — `kxSolveDepCW`,
  `kxDecideDLW`, `kxDecideDK0W`, `kxDecideDKSW` return the antiderivative data (the same
  square-root columns as `kxDecideCW`), agree with the deciders (`…_isSome`) and are valid
  (`kxDecideDLW_valid`, `kxDecideDK0W_valid`, `kxDecideDKSW_valid`). **Non-linear bases**
  (`Mixed/KFSquareOdd`): a rational non-square stays a non-square in every `Kₘ` when the base curve
  has odd degree in `y` (`not_isSquare_odd`, `not_isSquare_KF_odd`: `K(√δ)` would be a degree-`2`
  subextension of an odd-degree extension) and when it is `y² + c₁y + c₀` with discriminant
  `c₁² − 4c₀` squarefree and non-constant (`Mixed/KFSquareQuad`, `not_isSquare_KF_quad`: a root
  `a + by` of `X² − q` forces `q = a²` or `4q = b²D`, and `sqfree_not_sq`); the level-`m + 1`
  conjugation searches accept every base with `sqOK` (linear, odd degree, `quadOK`, or a smooth
  integral point found by `ptSearch`: `Mixed/KFSquarePoint`, **`not_isSquare_KF_point`** — around a
  smooth rational point `(x₀, y₀)` of a base monic in `y`, Hensel's lemma in the `X`-adically complete
  `ℚ⟦t⟧` embeds `K₀` into `ℚ((t))`, where a square root of a rational has a rational leading
  coefficient, `laurent_sq`). Not yet:
  curves constant in `tₘ` with non-rational coefficients in `Kₘ` (non-constant curves are
  settled by `ExH.hint_htor`, below), conjugation at levels `m + 1` over even-degree bases without a smooth rational point found by the
  search (e.g. pointless curves), completeness of the constant-curve searches over non-linear
  bases, kernel-checked theorems at levels `m + 1` with function-field height certificates (the
  constant-curve one is kernel-checked, `not_elementary_L1K`).
* **Manin map (started 2026-11-11).** For non-constant curves the route is Manin's theorem of
  the kernel. `Mixed/ManinGM` gives the Gauss–Manin vector `b(R) = ((u' + h(u))/v, (u u' + g(u))/v)`
  of `y² = x³ + A x + B` over any differential field. The coefficients `β = (9A'B − 6AB')/(2Δ)`,
  `α = −δ`, `γ` and the quadratics `h, g` reduce `∂ω, ∂η` modulo exact forms. Six polynomial
  certificates (`gm1/2` chord, `tm1/2` chord through a `2`-torsion point, `dm1/2` tangent) show
  that `b` is additive up to the coboundary `(−βc, c' − δc)`, with `c = −2λ` and `λ` the slope.
  `Mixed/ManinMap` defines the **Manin map** `mu R = D b₁ − κ b₁ + β b₂` with `κ = (Dβ + βδ)/β`
  on Mathlib's `W.Point`, for any `Derivation ℤ K K`, `char K = 0`, `4A³ + 27B² ≠ 0`. It proves
  **`mu_add`** (all cases of the group law; the `2`-torsion cases are reduced to `tm`), `muHom`,
  `mu_torsion`, and **`indep_of_wronskian`**: if `mu P · D(mu Q) − mu Q · D(mu P) ≠ 0`, then no
  relation `m P = n Q + T` holds with `T` torsion and `(m, n) ≠ 0`. This independence
  certificate is sound for non-constant curves. `Mixed/ManinCompute` makes it executable over
  `K(X)` with `D = d/dX` (`dX`). It provides the quotient rule on codes (`dFr`, `val_dFr`), the
  executable Manin map `muC` with **`val_muC`** (`val (muC …) = mu dX A B (u, v)`, side conditions
  checked by `muOK`), and the Boolean certificate `manCert` with **`indep_of_manCert`**.
  `Mixed/ManinExample` treats `y² = x³ − x + X²` with `P = (0, X)`, `Q = (1, X)`. It computes
  `mu P = −8/(X(27X⁴ − 4))` and `mu Q = 4(1 − 3X²)/(X(27X⁴ − 4))`, and proves **`indep_e`**:
  independence modulo torsion, kernel-checked in about 10 s, against about 2 min for the height
  certificate of `EllCertExample`. `Mixed/KXManin`, **`hgrp_of_manCert`**, wires the certificate
  into the `kx` exception: certificate points over `k₀(X)`, mapped along `j : k₀ → k` onto the
  `toShort`-images of `D, Z`, give the group condition `2N D + 2μ Z ≠ 0` of `kxe_norel_group`
  (no Liouville form). The decider uses it. `Mixed/KXCertBridgeM` defines `kxChkM` (= `kxChk`
  with `manCertP` in place of `certQ`) and `grp_of_chkM`. `Mixed/KXMWDecideM` defines
  **`kxDecideMW0M`**, which tries the Manin certificate first and then the height search, and
  proves it correct (`kxDecideMW0M_correct`). In `Mixed/KXMWExampleM`, the Manin branch alone
  decides `∫ √(e³ˣ − eˣ + x²)/(x(eˣ − 1)) dx` (`#guard`, `kmax = 0`). **`not_elementary_mwM`**
  proves it not elementary, kernel-checked in about 20 s. Completeness of the Manin
  certificate itself is **Manin's kernel theorem** (`mu R = 0` with `j` non-constant ⇒ `R`
  torsion), not proved here; it is no longer needed, since the height certificate is complete
  (`ExH.certQ_exists_nc`, below). **Levels `m + 1`**: `Mixed/KXMWDecideSM` defines `kxChkTSM` and `grp_of_chkTSM`,
  using `grp_of_chkT0S` with `indep_of_manCertP` over `Kₘ(t)`. It also gives `kxDecideMWSM`
  (Manin first, then `kxDecideMWS`) with `kxDecideMWSM_correct` and `not_elementary_of_MWOKSM`.
  `Mixed/KXMWExampleL1M` proves `∫ √(e^{3eˣ} − e^{eˣ} + e^{2x}) / (e^{eˣ} − 1) dx` not elementary
  (**`not_elementary_L1M`**): a non-constant curve at level `1`, with the whole Manin search
  kernel-checked in about 3 min. The function-field height certificates at this level were too
  slow even to evaluate.
  **Constant-ratio certificate and conditional completeness.** `indep_of_ratio`,
  `manCertR`/`indep_of_manCertR` and `manCertRP` cover `mu Q = c · mu P` with `c` a non-rational
  constant. `kxChkTSM` accepts either certificate; rationality is tested by `ratOfK`.
  `Mixed/ManinComplete` states **Manin's kernel theorem** as a hypothesis `MKT K` (not an axiom).
  It proves `const_of_dX` (the constants of `(K(X), d/dX)` are `K`) and `extract_const`, and
  then **`cert_complete`**: under `MKT K`, any two points independent modulo torsion are accepted
  by `manCert` or `manCertR`. Relation search plus Manin certificates therefore decide the
  Mordell–Weil exception for non-constant curves up to `MKT`,
  **when `j` is non-constant** (`β ≠ 0`) — a conditional statement superseded by the unconditional
  height completeness `ExH.certQ_exists_nc` (below); the Manin certificates remain as a fast path. Open: **isotrivial non-constant curves** (constant `j`,
  non-constant coefficients, e.g. `y² = x³ + t`). There `β = 0`, so `mu ≡ 0` and the Manin
  certificate never applies. The constant-curve branch needs rational coefficients and does not
  apply either. **Quadratic twists solved (2026-11-11):** `Mixed/RatComp` proves **`ht_comp`** /
  `ht_comp'`, multiplicativity of degree under composition, `ht (p(s)/q(s)) = max (deg p)
  (deg q) · ht s` for constant-coefficient coprime `p, q`. The proof uses homogenized Bézout
  identities and coprimality of reflections. `Mixed/EllIso` covers `A = a D²`, `B = b D³`. On
  `s = x/D` duplication is the degree-`4` map `dupP/dupQ`. Hence
  **`canonH_eq_gTw`**: the canonical height is the natural number `ht (x/D)`, and
  **`two_tors_of_canonH`**: positivity when `D³` is not a constant times a square.
  `Mixed/EllIsoGram` proves the quadratic-form expansion (`canonH_quad`), `disc_pos`
  (`4ac − b² ≥ 1` for independent points) and **`hgap_exists`**: the level-`k` certificate of
  `ell_indep` exists. The height search is therefore complete on quadratic twists without
  Lang–Néron or `MKT`. **All twists:** `Mixed/EllIsoGen` (`hgap_exists_gen`) shows that
  integrality of `k · canonH` plus positivity give a complete certificate.
  `Mixed/EllIso0` treats `y² = x³ + B` with `s = x³/B` and duplication
  `s (s − 8)³/(64 (s + 1)³)`: `canonH = ht (x³/B)/3`, height `0` only on `2`- and `3`-torsion
  when `B` is not a constant times a cube, and `hgap_exists_0`. `Mixed/EllIso1728` treats
  `y² = x³ + A x` with `s = x²/A` and duplication `(s − 1)⁴/(16 s (s + 1)²)`:
  `canonH = ht (x²/A)/2`, positivity when `A` is not a constant times a square, and
  `hgap_exists_1728`. The excluded cases are quadratic twists (`EllIso`). So on every isotrivial
  non-constant curve the height certificate is complete, unconditionally. `Mixed/EllIsoCert`
  proves **`certQ_of_hgap`**: the executable check `certQ` is exactly the real inequality, so
  `certQ` passes at some level for independent represented points (`certQ_exists_quad`,
  `certQ_exists_0`, `certQ_exists_1728`). The reduction for constant `j` is done:
  `Mixed/EllIsoNormal`, **`iso_normal_form`**: `A³ = r B²` with `A, B ≠ 0` gives `A = r D²`,
  `B = r D³` with polynomial `D`, using integral closedness of `K[X]`.

  **The decider-level theorem without shape conditions (2026-11-11).**
  `Mixed/KXNonConstDecide4`, **`kxDecideNCS3_decides`**: the non-constant decider at levels
  `m + 1` answers for all large bounds, and correctly, given
  any sound and complete recursive checks over `Kₘ` (unconditionally since 2026-11-25). This removes the per-class hypothesis
  (non-trivial twist or non-constant `j`) of `kxDecideNCS2_decides`.
  **`kxDecideNCS3_decides_lin`** is the instance with the tower check `recKF` over a linear base.
  It has no hypotheses beyond the decider's data. The pieces:

  - **Classification.** `Mixed/EllIsoClassify` proves `const_j_classify`: constant `j` gives a
    non-trivial twist or a curve constant up to scaling (`A = u⁴a`, `B = u⁶b`). For the second
    case, `Mixed/ConstScaleDescent` proves that every point descends (`ΦCS`, bijective), so the
    Mordell–Weil question drops one level.
  - **Executable tests.** `Mixed/JTest` (`jConstB`: a failing test gives `β ≠ 0`),
    `Mixed/PolyRoot` (`rootP`, n-th roots in `K[X]`, sound and complete) and `Mixed/ClassifyCS`
    (`csData`: the scaling `u`, sound and complete, `csData_complete`).
  - **One step.** `Mixed/IndepDesc` and `IndepStep`/`IndepStep2` define `stepI`/`stepI1`: Manin
    certificates, then `certQ` heights, then descent and a recursive call.
    **`stepI_complete`** proves completeness **unconditionally**: a curve constant up to scaling
    descends (`csData_complete`), and on every other curve the height certificate exists
    (`ExH.certQ_exists_nc`).
  - **Exact canonical heights (2026-11-25, `Mixed/ExH*.lean`, standard axioms).** For
    `y² = x³ + A x + B` over `K(X)` (`K` any field of characteristic `0`), not constant up to
    scaling, **`ExH.hint_htor`**: some `k > 0` makes `k · ĥ` natural-valued and `ĥ(P) = 0` only
    for torsion `P` — the positivity usually obtained from the Lang–Néron theorem, proved here
    elementarily. *Local part*: for a valuation `v` of residue characteristic `0` and an
    integral model, a point is singular at `v` if `x` is integral and `f(x), f′(x) ∈ 𝔭`; without
    `y`-coordinates or residue fields, `x(P ± Q)` are the roots of `T² − sT + p` with
    `s·(x₁−x₂)² = 2(x₁x₂+A)(x₁+x₂)+4B`, `p·(x₁−x₂)² = (x₁x₂−A)²−4B(x₁+x₂)` (`ExH.xpm`); hence the
    non-singular points form a subgroup `E0` (`ExH.sing_pm`), and for a *minimal* model every
    point has a multiple `m ≤ 2v(Δ)+14` in `E0` (**`ExH.local_index`**: pigeonhole on multiples,
    `exists_nsmul_mem`, with a case distinction by reduction type — II, II* have no singular
    points by parity of `v(y²)`; III, IV, IV*, III* have one class; I₀*/Iₙ* by Lagrange
    interpolation and the centre `e = −3B/(2A)`; multiplicative by the classes `v(x − e)`).
    *Global part*: the places of `K(X)` are the irreducible polynomials and `∞`
    (`ExH.Vp`, `ExH.Vinf`; no algebraic closure), a uniform exponent `N` puts `N • P` into
    `E0` at all places (`exists_exponent`), and there the weighted height
    `max (deg num x) (deg den x + 2n)` quadruples **exactly** under doubling (`sH_double`:
    `x(2P) = Φ/(4eF)` is in lowest terms and the leading forms do not both drop), so
    `ĥ = ` weighted height `≥ 2n > 0` (`canonH_eq_sP`); non-minimal models reduce by scaling
    (`min_model`, `canonH_scale`). **`ExH.certQ_exists_nc`**, **`certQ1_exists_nc`**: the
    executable height certificates exist.
  - **Lift and recursion.** `Mixed/IndepLift` lifts a curve over `K ↪ K'(X)` to a polynomial model
    (`lvlI`). `Mixed/IndepQ` handles the bottom over `ℚ` (`recQ`: integral scaling plus
    `certG`/`certH`, complete by Northcott). `Mixed/IndepTower` builds **`recKF`**/`recKF1`: lift
    `Kₖ₊₁ → Kₖ(X)` by `RFC.canon`, and `K₀ → ℚ(x)` by `psiLin`. Soundness and completeness are unconditional.

  **Level 0** (`ks 0` exponential, curve over `ℚ(x)`), in `Mixed/KX0NonConstSide{,2,3}`,
  `KX0NonConstRec` and `KX0NonConstDecide`. The short model is over `ℚ[X]`, so the recursion
  bottoms out at once in `recQ`. **`kxDecideNC0_decides`** covers any cubic: constant
  coefficients or not, any `j`, any number of class generators. It has no extra hypothesis.

  **One entry point and one search bound (2026-11-15).** `Mixed/KXAllLevels` defines
  **`kxDecideNC`** at every exponential level over a linear base: level `0` uses `kxDecideNC0`,
  and level `m + 1` uses `kxDecideNCS3` with `recKF`/`recKF1`. **`kxDecideNC_correct`** proves
  correctness of every answer; **`kxDecideNC_decides`** combines the completeness
  theorems, with no Manin kernel hypothesis.
  `Mixed/KXSearch` turns the three nested search bounds into a single bound: **`kxSearch`**
  enumerates triples `(Bd, nmax, kmax)` using natural-number pairing and keeps the first answer.
  Simply setting the three bounds equal is not justified by the nested completeness theorem.
  **`kxSearch_correct`** proves correctness at every bound; **`kxSearch_mono`** proves that an
  answer persists unchanged; **`kxSearch_decides`** proves eventual success under the same
  hypotheses and for suitable residue-specialization data `rs` (still existential, not computed
  by this wrapper). `Computable/PrefixSearch` supplies the generic finite-prefix search proofs.
  `Mixed/KXSearchExamples` checks both answers for dependent classes at level `0`, the Manin
  branch at level `1`, and a search whose only successful triple is off the diagonal.

  **Automatic residue data and expression dispatch (2026-11-16).** `Mixed/KXResidues` proves
  **`kxDecideNC_congr_prefix`**: a level-`m` attempt reads only entries `0, …, m` of `rs`.
  `Computable/NatSeq` enumerates every finite prefix (`natSeq_complete`), so **`kxAuto`**
  (`Mixed/KXAuto`) searches both the residue choices and the three numeric bounds. Its caller
  supplies only the input and one search bound. **`kxAuto_correct`** proves every returned
  answer correct, **`kxAuto_mono`** preserves it at larger bounds, and **`kxAuto_decides`**
  proves eventual success under the same cubic input conditions, now
  **without any supplied or existential residue data**. This is an exhaustive search, not a
  practical bound on runtime. `Mixed/KXAutoExamples` checks a positive encoded stage and an
  automatic negative answer.
  The pole-expression parser has a verified exponential-solver interface (`frontSqrtPEWith`,
  `SqrtPoleExpSound`); the original `frontSqrtPE` and its witness interfaces retain their
  behavior. `Mixed/FrontSqrtPoleNC` adds **`frontSqrtPNCE`**, dispatching exponential levels to
  `kxDecideNC`, and **`frontSqrtPAuto`**, building the expression tower and searching residue
  choices and bounds automatically. **`frontSqrtPAuto_sound`** proves every answer correct. `Mixed/FrontSqrtPoleNCExamples` checks both answers for dependent classes on
  `θ² = e³ˣ − eˣ + 1`, and an automatic negative answer for
  `∫ √(e^(3eˣ) − e^(eˣ) + e^(2x))/(e^(eˣ) − 1) dx`.

  **Completeness from checked expressions (2026-11-16).** `Mixed/FrontSqrtPoleNCComplete`
  proves finite residue dependence for both parser branches and that the automatic search
  reaches any successful attempt using `primesBelow bound`. With a realization, it eventually
  returns the same Boolean answer (`frontSqrtPAuto_decides_of_attempt`), including `false`.
  `Mixed/KXInputCheck` makes the cubic solver's additional input conditions executable.
  **`frontSqrtPCubicCheck`** (`Mixed/FrontSqrtPoleAccepted`) runs the parser with this checking
  backend and requires an exponential top level. **`frontSqrtPAuto_decides`** proves that every
  expression passing the check eventually receives a persistent, correct answer,
  unconditionally. No successful attempt, residue function, or auxiliary
  search bound is assumed. A passing check establishes eligibility for this completeness
  theorem, not elementary integrability; a failing check does not imply non-elementarity.
  The examples cover accepted positive and negative inputs at two levels and reject degree
  five, missing pole data, and a logarithmic top level.

  Thus, for cubic radicals over a linear base, at every exponential level and under the stated
  input conditions, the Mordell–Weil exception is **decided unconditionally** (standard axioms):
  Manin's kernel theorem is not needed, the canonical height being integral and positive off
  torsion (`ExH.hint_htor`). These completeness theorems do not cover
  non-linear base curves or general higher-genus radicals. `kyDecide` still answers `none` when
  a component is not torsion and neither killing argument over `t = 0` applies. In that case,
  whether a ℤ-combination of the divisors
  is torsion is not decided (it needs relations in the Mordell–Weil group of a curve over a
  function field). The same question limits the non-Kummer decisions with several places at
  infinity or above `0`: they need S-units whose divisors span the places' degree-`0` lattice
  over `ℚ`, and when the classes are not all torsion no such units exist. At a **logarithmic** level
  this is not a Mordell–Weil question: at a place `P` above `t = ∞` (`τ = t^{−1/e}`) the
  `τᵉ`-coefficient of `f = Y′ + ∑ cᵢ uᵢ′/uᵢ` satisfies `f_e + ρ_P t′ ∈ K_P′` with
  `ρ_P = ∑ cᵢ ord_P(uᵢ)/e`, and `ρ_P` is unique (`t` is transcendental over `K_P`), so the residue
  divisor is computable and only single-divisor torsion tests over `Fₘ` are needed. Proved
  (`Mixed/NKResInf`): the residue formula `coeff_liouville_top` (via the truncated logarithm
  `coeff_logDeriv_top` and uniqueness `residue_unique`), and `nk_liouville_noRes`: if all residues
  at infinity vanish, `f = v′ + ℓ` with `ℓ ∈ C` — no logarithm, no unit needed. The proven
  code-level residue test for split places at infinity (`Mixed/NKResSplit`, `Mixed/NKResCodes`):
  invert `Q(T, Z) = T^{ns} P(1/T, Z/T^s)`, Hensel roots at `T = 0` (`split_inf_inv`, truncations
  unique by `hensel_trunc`), residue coefficient `∑ f_{ji} [T^{1+i+sj}] Θʲ`, and a derivative test
  through the Risch differential equation solver; `splitResCk` certifies that all residues vanish
  (`zero_res_codes`). Decider (`Mixed/NKInfRVG0`, `Mixed/NKDecidesInfVG0`): when `splitResCk`
  passes (Newton lifts found by `henselC`, `splitRes0C`), `nk_iffInfVG0` / `nk_decidesInfVG0`
  decide `∫ ∑ bⱼ θʲ` with `exactTLVG` **without any units**, whatever the unit rank. Examples
  (`Mixed/NKZeroResExamples`): `∫ √(log² x + x) dx` and `∫ log x · √(log² x + x) dx` are not
  elementary, with no unit supplied. **Ramified places** (single slope `s/e`, `gcd(s, e) = 1`):
  along `t = T^{−e}` the curve is the expanded curve `P(xᵉ, θ)` along `x = T⁻¹`
  (`infSub_comp_expand`, `Mixed/NKResRam`), and `Q(wT, wˢZ) = w^{ns} Q(T, Z)` for `wᵉ = 1`, so a
  Hensel root `Θ` gives the conjugate roots `w^{−s} Θ(wT)` with the same residue
  (`fibre_root_conj`, `zero_res_ramConj`, `Mixed/NKResRamConj`): **one rational residual root per
  place** suffices (`splitResRamCk`, `zero_res_ramConjC`). Decider `nk_iffInfVR0` /
  `nk_decidesInfVR0` / `nk_decidesInfVR0P` (`Mixed/NKInfRVR0`, `NKDecidesInfVR0`, `NKRamZeroCand`:
  units-free gauge candidates). Example (`Mixed/NKZeroResRamExamples`): for
  `θ⁴ − 5 log x θ² + 4 log² x + x log x = 0` (two places at infinity, each ramified),
  `∫ θ dx` is not elementary, with no unit. **Several Newton segments** (any rational slopes
  `sₖ/eₖ`, `Mixed/NKResMulti`, `NKResMultiC`): per segment the polynomial
  `Q(τ, Z) = τ^{K₀} P(τ^{−e}, Z τ^{−s})` (`segPoly`, not monic) has the power-series root
  `Θ = T^{ds} ρ` of each branch rotated to leading coefficient `β ∈ Fₘ` (`segPoly_root`, rotations as
  in `rot_of_pow_eq`); Hensel uniqueness needs no monicity (`seg_trunc`), and the residue at `T^N` is
  `∑ fⱼₗ [τ^{e+el+sj}] Θ̃ʲ` (`coeff_eval_seg`, `zero_res_multi`); certificate `multiResCk`
  (`zero_res_multiC`), deciders `nk_iffInfVMR0`, `nk_decidesInfVMR0` (`Mixed/NKInfRVMR0`,
  `NKDecidesInfVMR0`). Example (`Mixed/NKZeroResMultiExamples`): `∫ θ dx` for
  `θ³ − θ log x + x log x = 0` is not elementary, without the unit. **Units matching the
  residues** (`Mixed/NKResOrd`, `NKResOrdC`, `NKInfRVMR1`, `NKDecidesInfVMR1`): instead of
  `∑ₖ |Γₖ| − 1` independent units, any units `wᵢ = Uᵢ/dᵢ` and rationals `κᵢ` with
  `[T^N] f + (∑ κᵢ ord wᵢ)/N · η` a derivative at every place (`res_match_multi`; orders certified
  by coefficient windows of the truncations, `order_eval_seg`, `ordCk`; certificate
  `multiMatchCk`) give `f = v′ + ∑ κᵢ wᵢ′/wᵢ + ℓ` (`nk_liouville_resU`, via `logSum_qindepP`, a
  version of the `ℚ`-independence reduction keeping "no zeros or poles at the finite places"), so
  `nk_iffInfVMR1` / `nk_decidesInfVMR1` decide with the exact-part test on those units only. An
  elementary `f` has rational residues `ρ_P` and a `ℚ`-principal residue divisor, so such units
  exist over `Fₘ` whenever `f` is elementary (or its residue divisor is torsion) — as codes only
  after a descent to the code field, not yet formalized (see below); the remaining case is a
  non-torsion residue divisor. Example (`Mixed/NKResMatchExamples`): for `θ² = log² x (log² x + x)`
  and `f = (log x/x³) θ` (residues `∓1/8`, `κ = −1/16`), `∫ f` is not elementary. **No rational
  residue** (`Mixed/NKResNone`): the residue of a Liouville form at a place at infinity is a constant
  of `Fₘ` (and antiderivatives descend from the algebraic closure, `not_deriv_of_integral`), so if
  the parametric Risch equation for `[c, η]` at some place has only solutions with zero first
  coordinate (`noResCk`), `∫ f` is not elementary (`nk_not_elem_noRes`; `coeff_place_multi` gives a
  root at every place with the computed residue coefficient). Example
  (`Mixed/NKResNoneExamples`): `∫ 8 log x √(log² x (log² x + x))/(x² (x + 1)) dx` is not
  elementary. The Newton lifts always pass the truncation checks (`Mixed/NKNewton`,
  `segHenselC_truncOK`), and a unit without zeros or poles at the finite places can be normalized
  to a trace-free logarithmic derivative (`Mixed/NKNormUnit`: its norm is a constant,
  `norm_const_of_unitFin`, `normalize_unit`), and the residue divisor of an elementary integrand
  is `ℚ`-principal (`Mixed/NKResPrinc`, `exists_unit_of_residues`: a unit with orders
  `M N ρ_r` at the places at infinity). **Non-constant curves with two places at infinity**
  (`Mixed/NKInf2K`): the curve translated to the computable code field `Kₘ = KF Fc m`
  (`trCurveK`, realized by `psiC`), its inverted curve certified to have a non-torsion difference of
  the two places (`TwoPlaceCertK`, over `Kₘ`): the units are constants (`nk_liouville_two`), and
  `nk_iffInf2K` decides with the exact part and no units. **Example** (`Mixed/NKInf2KExample`,
  data and kernel checks in `NKInf2KExData`, `NKInf2KExChk1`–`6`): `θ² = t⁴ − x t³ − x t² + x t + 1`
  over `t = log x` (genus one, `x`-dependent), the certificate over `K₀ = ℚ(x)` generated and
  checked by the kernel — integral basis with no special points (`globalCheckR`), place series by a
  square-root recurrence, primes `7`, `37` with orders `3`, `4` (explicit ramified branches);
  `∫ θ dx` is not elementary (`not_elementary`; the `exactTLVG` answer is a `#guard`-checked
  hypothesis, its kernel evaluation exceeding the memory budget). Certificate generation over
  `Kₘ` is not automated (curve-specific choices: primes with split, square-derivative reductions
  and small coprime orders, chosen by an external search). **Exponential levels**
  (`Mixed/NKInf2KExp`): the same for `θ` over an exponential level with a single place above
  `t = 0` (`nkShape0`) — `nk_iffET2K`, `nk_decidesET2K` (exact part by `exactT`); and with the
  gauge/rescaled test `exactTLEVG` at infinity, needed when the limit matrix is not triangular in
  the given basis (`Mixed/NKInf2KExpV`, `NKInf2KExpVIff`: `nk_iffET2KV`). **Example**
  (`Mixed/NKInf2KExpExample`, data and kernel checks `NKInf2KExpExData`, `NKInf2KExpExChk1`–`6`):
  `θ² = t⁴ − t³ + 2t² + x² t` over `t = eˣ`, certificate over `ℚ(x)` with primes `13`, `41`
  (orders `3`, `4`); `∫ θ dx` is not elementary, with no computational hypothesis:
  `NKInf2KExpExThm.not_elementary_full` (the `exactTLEVG` answer by `decide +kernel` in
  `NKInf2KExpExRes`, about 6 min and 65G, on a rented machine; control `θ′` exact). **Kernel-checked exact parts.** With `linSolve` structural (fuel,
  irreducible for the elaborator) the whole exact-part test reduces in the kernel; the smaller
  example `NKInfRVExpExample` (`θ² = t² + x t` over `eˣ`) is now a theorem with no computational
  hypothesis: `Mixed/NKInfRVExpExRes` (`exactTLEV … = some false` by `decide +kernel`, about 6 min,
  30G peak) and `NKInfRVExpExThm.not_elementary` (**`∫ √(e²ˣ + x eˣ) dx` is not elementary**, every
  input of `nk_iffETInfV` kernel-checked). The same holds for two constant-curve exp examples:
  `Mixed/NKInf2ExpExThm.not_elementary_full` (**`∫ √(eˣ(1 + 25eˣ)(1 − 2eˣ)(1 − 50eˣ)) dx` is not
  elementary**) and `Mixed/NKInf2NExpExThm.elementary_full` (**`∫ √(eˣ − e²ˣ) dx` is elementary**),
  their `hres` proved by `decide +kernel` in `NKInf2ExpExRes`/`NKInf2NExpExRes` (≈ 6.5 min, < 40G
  each). **Staged kernel checks** (`Mixed/NKStageC`, `NKStageC2`, `NKStageE`): the kernel keeps
  every reduction of one declaration, so the exact-part test is split into stages, each a
  `decide +kernel` check against literal data in its own lemma (system set-up, indicial bound,
  `wSys`, each degree step of the coefficient loop with the residual of every basis element and each
  component of the lower solver separately, the final residuals, each coordinate of the relation
  search), assembled by the stage theorems (`exactC_stage`, `exactTL_stage`, `exactC2_stage`,
  `primSysC_stage`, `expSysT_stage`, `loopC_kstageR`, `relRun_stage`, …). The stage modules are
  generated (literals printed by native evaluation, then re-checked by the kernel). With them
  `NKInf2ExThm.not_elementary_full` (13 min, 15G), `NKInf2NExThm.elementary_full` (10 min, 20G)
  and `NKInf2UExThm.not_elementary_full` (8 min, 12G) carry no computational hypothesis.
  Likewise `NKInfRExThm`, `NKInfRNExThm`, `NKInfREExThm`, `NKInfRNEExThm` (the `NKInfR`, `NKInfRN`,
  `NKInfRExp`, `NKInfRNExp` examples: 40, 48, 10 and 13 min, about 70G each — checked on a rented
  120G machine; building them needs that much memory). The log-level genus-one example `NKInf2KExample` still exceeds the memory
  budget (kernel cost ≈ 60 µs per unfolding; the unnormalized fraction codes make even `θ′` cost
  ~150k rational operations). `Mixed/NKStage` (`exactTLVG_stage`) splits the test into the change of
  basis and the solver so each stage can be checked against literal data in its own declaration;
  the direct kernel check of `NKInf2KExample` exceeds even 112G, and each stage alone still exceeds 32G, so witness inputs (checked `θ′`, as in
  `traceW`) and staging inside the degree loop of the solver are needed. Certificate generation for `y² = Q` over a code field is
  automatic (`Mixed/NKCertKF`, `NKCertKFAuto`: square-root series, explicit ramified branches modulo
  `p`, `primeCertG`; `primeCandsK` searches primes `p` and specializations `x ↦ x₀` with `Q` split
  and square derivatives, computing `m_p`; `pickPairK` picks the pair with the smallest
  `pairMult` whose test fails; `autoTwoK` does everything): on the two examples it finds
  `(13, 41)` and `(7, 17)` in about a minute each. The answer is untrusted and checked. Not yet done: the existence theorem for matching
  certificates (the Liouville units have coefficients in `Fₘ` over the full constant field, so a
  descent to the code field is needed), torsion tests over `Fₘ` for non-torsion residue divisors,
  places whose residual roots have no rational `e`-th root, and the exponential level (where the
  coefficient at `T⁰` involves logarithmic derivatives of leading coefficients). At an **exponential** level the residues above `t = 0`
  and `∞` are only defined modulo `a′ ∈ K′`, and the question is whether the residue divisor lies
  in the span of the special places plus torsion — a Mordell–Weil relation question.
  Started on that question (generic, proved, standard axioms): `Mixed/MWIndep` and `Mixed/MWPair`
  show that a non-zero Gram determinant of a symmetric ℤ-bilinear pairing rules out every relation
  `m • D = n • Z`. `Mixed/MWTate` builds the canonical height from any naive height with bounded doubling
  defect (Tate's telescoping: `abs_canon_sub_le`, `canon_double`, `canon_unique`). `Mixed/MWPair` turns
  a bounded parallelogram defect into an exact bilinear pairing and gives a checkable certificate
  `indep_of_approx` (approximations `h(2ᵏP)/4ᵏ` with explicit error `C/(3·4ᵏ)`). `Mixed/FFHeight` is
  the naive height on `K(X)` (invariant under extension of constants, `Mixed/FFBase.ht_map`). **Genus one, done** (`Mixed/FFMorph`, `EllDup`, `EllHeight`, `EllParAux`,
  `EllPar`, `EllNT`, on Mathlib's group law of `y² = x³ + A x + B` over `K(X)`, `char K = 0`): the naive
  height `hN P = ht (x P)` has doubling defect `≤ 11 D` (`hN_double`, via Silverman's resultant
  identities checked by `ring`) and parallelogram defect `≤ 12 D` (`hN_par_upper` through the Gauss
  lemma for the roots `x(P ± Q)` of `W₀X² − W₁X + W₂`, then `hR_par`), `D = max (deg A) (deg B)`; so
  the Néron–Tate pairing `ntPairing` exists on `E(K(X))` and `ell_indep` is a checkable independence
  certificate. Any short curve over `K(X)` reduces to polynomial coefficients by the scaling
  `(x, y) ↦ (u²x, u³y)`, an injective group homomorphism of points (`Mixed/EllScale`: `scaleHom`,
  `scaleHom_injective`, `exists_poly_scale`, `indep_of_scale`; Mathlib has no such isomorphisms), and a cubic model
  `θ² = c₃t³ + c₂t² + c₁t + c₀` reaches short form by `X = c₃t, Y = c₃θ` (`cubic_to_W`) and the
  translation `X ↦ X + a₂/3`, again an injective group homomorphism (`Mixed/EllTrans`: `transHom`,
  `indep_of_trans`). Points over a quadratic extension `K' = F(√d)` reduce to `F`: σ-fixed points descend
  (`Mixed/EllDescent`: `fixed_descends`), anti-fixed points come from the twist `y² = x³ + d²a x +
  d³b` (`anti_descends`), and relations transfer to the descents of `D ± σD`, `Z ± σZ`
  (`indep_of_trace`, `indep_of_twist`). The complete test over `F(√d)`: the trace `traceHom` and the
  twist descent `twistDesc` (`ι⁻¹(P − σP)`, through the injective twist homomorphism `twistHom`,
  `anti_in_range`) are homomorphisms `E(F(√d)) → E(F)`, `E^d(F)`, and a non-zero Gram determinant of
  the sum of the pulled-back pairings rules out every relation (`Mixed/EllCombine`, `Mixed/EllTwist`:
  `indep_of_pulls`, `quad_indep`); `quadPair` iterates along towers `F ⊂ F(√d₁) ⊂ F(√d₁, √d₂) ⊂ …`.
  **Missing:** Jacobians of higher genus (`θⁿ = A(t)` beyond genus one), the
  transformation of the genus-one curves `θ² = A(t)` (`deg A = 3, 4`) to Weierstrass form over the
  function field `Kₘ` (not `K(X)`), and the wiring into `kxDecide`/`kyDecide`.
* **Units outside the order `Fₘ[t][θ]`.** The unit certificates of the non-Kummer deciders
  (`unitC`: `U·V ≡ 1 mod P` with `U, V ∈ Fₘ[t][θ]`) see only units of that order. When the order
  is not integrally closed, a unit of the integral closure may have no power in it (the quotient of
  the unit groups can have a torsion-free unipotent part in characteristic 0). In that case the
  `hunits` hypothesis fails although enough units exist, and the decider does not apply. Started:
  units `U/d` with integrality certificates (`unitsCD`, `Mixed/NKUnitsCD`: `U·V ≡ d²`, `U/d` and
  `V/d` roots of monic polynomials over `Fₘ[t]` checked in Horner form (`unitIC`, `Mixed/NKUnitIC`,
  `Mixed/NKHornerInt`), `g·d² ≡ U′V − d′d`). Regularity at finite branches follows from
  `regularFinite_of_horner`. Done for split, ramified and several-slope places at infinity, logarithmic and exponential
  levels (`nk_decidesInfVGD`, `nk_decidesETInfVGD`, `nk_decidesInfVRD`, `nk_decidesETInfVRD`,
  `nk_decidesInfVMRD`, `nk_decidesETInfVMRD`; `Mixed/NKInfRV*D`, `NKDecides*D`). **Such certificates
  always exist** (`unitsCD_exists`, `Mixed/NKUnitsCDExists`): for any units `uᵢ` of the integral
  closure with code coordinates (`uᵢ = pᵢ(θ)`, `uᵢ⁻¹ = qᵢ(θ)`, both roots of monic polynomials over
  `Fₘ[t]`), clearing denominators (`clear_den`) gives `Uᵢ, Vᵢ, dᵢ`, and every check is complete
  (`zeroModC_complete`, `unitCD_complete`, `unitIC_complete`, `logDerChkD_complete`). S-units above `t = 0` likewise: `uᵢ = (Uᵢ/dᵢ) t^{−jᵢ}` with
  `(Uᵢ/dᵢ)(Vᵢ/dᵢ) = t^{kᵢ}` (`unitsC0D`, `Mixed/NKUnits0D`), deciders `nk_decidesETInf0D`,
  `nk_decidesETInf0RD`, `nk_decidesETInf0MRD`, existence `unitsC0D_exists` (`Mixed/NKUnits0DExists`).
  Constructive (antiderivative-returning) versions with denominators: `nk_integrateInfVMRPWD`,
  `nk_integrateETInfVMRPWD` (`Mixed/NKMultiRWitD`), `nk_integrateETInf0MRPWD`
  (`Mixed/NKMultiR0WitD`); the log terms are `log(Uᵢ/dᵢ)` (`units_logsD`, `units0_logsD`,
  `Mixed/NKUnitsLogsD`). The several-slope shape (`multiShapeRC`) also covers a single split
  (`e = 1`) or ramified slope, so these subsume the split and ramified cases. Example (`Mixed/NKUnitsDExamples`, `#guard`,
  ~1 min): over `t = log x`, `θ² = t²(t² + x)`; the unit `ũ = −(θ/t + t)²/x` (norm `1`) is not in
  `Fₘ[t][θ]` (no power of `θ/t + t` is); with `U, V, d = t²` and the monic relation
  `Z² + (2 + 4t²/x) Z + 1` the checks pass, and **`∫ log x · √(log² x + x) dx` is not elementary**
  (`searchIVMPD … = some false`), controls `ũ′/ũ`, `θ′` found.
* **Completeness of the torsion oracles over function fields** — done (square roots and
  radicals of any order, all mixed deciders; exceptions only in the Mordell–Weil cases). The deciders are parametrized by a certificate provider
  (`keDecideC`, `kqDecideC`, `kqmDecideC`, `kxDecideC`; the old names use the search provider).
  With **local certificates** (`localCert`, `Algebraic/SupLocalCert`: the base points are taken
  among all points of the reduced curve over `𝔽_p`, which exist by Stepanov's elementary Weil
  bound `Weil/Stepanov1–6`, `many_squares`) the oracle over the tower fields `Kₘ` eventually
  answers: `torsOracleLocal_eventually` (any characteristic-`0` field with eventually integral
  data), `kf_torsLocal_eventually` / `kf_torsLocal_exists` (`Mixed/KFSpec`, `Mixed/KFSpecExist`:
  reductions `redAtKF` at integer residues `rs`; outside a finite set of residues the specialized
  base curve is separable — resultant argument, `fSpec_good` — so infinitely many primes admit a
  simple root, `baseOK_infinite_good`; residues making any finite set of tower elements
  specializable exist, `exists_rs`). Consequently **`ke_decided`, `kq_decided`, `kqm_decided`**
  (`Mixed/KEDecides`, `KQDecides`, `KQMDecides`): for accepted data there are residues `rs` such
  that for every large bound `keDecideL`/`kqDecideL`/`kqmDecideL` answer, and correctly; and
  **`kx_decided`** (`Mixed/KXDecides`): `kxDecideL` answers correctly unless `P₊ − ∞` and a pole
  class are both certified non-torsion (the Mordell–Weil case above). For radicals of order
  `n > 2` the oracle side is done too: Stepanov's method for `n`-th powers (`Weil/StepanovN3–6`:
  an `n`-component auxiliary polynomial, independence by a determinant whose `P`-adic valuation has
  a unique minimal term, `many_nth_powers`), local certificates for `n ∣ p − 1`
  (`localCert_isSomeN`, `Algebraic/SupLocalCertN`), the eventual answer `torsOracleLocalN_eventually`,
  simultaneous simple roots of two polynomials modulo infinitely many primes
  (`exists_simple_roots_prime`, primitive element + Gauss's lemma, `Algebraic/SupSimpleRoot2`), and
  for the cyclotomic code fields `Kₘ(ζₙ)` `kfz_query_els` (`Mixed/KRSpec`). The runtime checks of
  `krDecide` after a torsion answer always pass: the norm of the witness descends to `Kₘ`
  (`descendNF_normNF_isSome`: the `φ(n)` embeddings `ζ ↦ ωᵛ` fix its coefficients,
  `Mixed/KRDescend`) and the gcd in the column computation is constant (`kr_gcd_coprime`:
  `Yⁿ − Â` is prime over `Kₘ(ζ)[t]` by Eisenstein and divides no conjugate of the witness,
  `Mixed/KRGcd`, `KRGcdT`). Hence **`kr_decided`** (`Mixed/KRDecides`): radicals `θⁿ = A(t)` over
  an exponential level are decided by `krDecideL`. With ordinary poles, **`ky_decided`**
  (`Mixed/KYDecides`; `kyDecideC` takes a provider, `kyDecideL` uses local certificates):
  for accepted data (`kyConst → kyFieldOK`) there are residues such that for every large bound
  `kyDecideL` answers correctly, unless a component is certified non-torsion while the orders over
  `t = 0` cannot be killed (the Mordell–Weil case above, stated exactly: an `ℓ`-th root of `A(0)`
  for a prime `ℓ ∣ n` but no `n`-th root, or a point `(0, ζᵏ)` of the twist certified
  non-torsion, `kyZeroQ`). The points over the poles are checked as points of `yⁿ = A` over
  `Kₘ ⊗ N` itself (`ky_ptsM`: the field identities are read at the root `X` of `M`,
  `aeval_gammaM`), and the column gcd is constant by `ky_gcd_coprime` (`Mixed/KYGcd`). Over a linear base the number field need not be supplied: **`ky_decided_linear`** (`Mixed/KYFieldExists`) — a field `ℚ[X]/(M)` with a primitive `n`-th root of unity and `n`-th roots of the `κ_q` always exists (`ky_field_exists`: primitive element of `ℚ(ζ, γ_q) ⊆ ℚ̄`, `M` its minimal polynomial) and stays irreducible over every code field (`liftQ_irr_linear`).
  With poles in `Kₘ ⊗ N`, **`kz_decided`** (`Mixed/KZDecides`; `kzDecideC`/`kzDecideL`) gives the
  same statement. The decision is about codes, so its facts are read in a realization of the tower
  over a splitting extension that contains a constant root of `M` (`exists_root_tower`, no
  integrability hypothesis needed). There the points over the poles are valid (`kz_ptsM`). After a change
  of base curve, **`kz_decided_bc`** (`Mixed/KBDecides`) gives the same statement. So the
  torsion oracles of all the mixed deciders over function fields now answer. The only exceptions
  are the stated Mordell–Weil cases of `kxDecide`, `kyDecide` and `kzDecide`.
* **Transcendental towers over conics without a rational point** — no longer a gap: such a conic
  is an ordinary base curve over `ℚ` for the mixed-tower decision (`elM_decides_any`), which
  needs no rational point (`Mixed/ConicExamples`: on `y² = −x² − 1`, `∫ log x/y` is not elementary,
  `∫ x log x/y` is; `elM` answers, correct for every large search bound). Only the older
  genus-`0` reduction by parametrisation (`genus0_pt_decides`) needs the point.

## General algebraic curves

`Curves/` treats an arbitrary curve `F(x, y) = 0` (`F` monic in `y`, irreducible over `C(x)`),
given as `CurveData C L`, and integrands `f = A(x, y)/D(x)`. Everything is proved from local
expansions (Newton–Puiseux, `Curves/Puiseux.lean`, `Branch.lean`):

* **Theory**: branches as differential embeddings into Laurent series (`embG`), integrality from
  branch regularity (`Integral.lean`, `Infinity.lean`), residue-free Liouville forms are exact
  (`SecondKind.lean`), local pole bounds (`Poles.lean`), the exact-part ansatz
  `W(x, y)/(disc · D)` with degree bounds (`Ansatz.lean`), Abel's direction (`Abel.lean`), the
  Liouville lift to the constants of an elementary extension (`Lift.lean`), and reparametrization
  of branch systems (`Reparam.lean`) so that one certified system per point suffices.
* **Certificates**: truncated Puiseux expansions at the special points (roots of `D · disc`) and
  above infinity, checked by a quantitative Hensel argument (`CertBranch.lean`, `HenselQ.lean`,
  `InfEval.lean`); the discriminant and norms `Res_Y(F, W)` by interpolation (`DiscC.lean`,
  `NormC.lean`); covering of the special points (`Cover.lean`).
* **Residue-free decision** `CurveProb.decideRF` (`ProcRF.lean`): exact part by linear algebra on
  the branch expansions, residues, symbolic zero test mod `F`.
  **`decideRF_spec`** (`ProcRFDecide.lean`): `decideRF = some b ⇒ (HasElementaryIntegral f ↔ b)`,
  over any algebraically closed constant field containing the (computable) coefficient field.
* **Logarithmic part** `CurveProb.decideLog P ws` (`ProcLog.lean`): with `ℚ`-coordinates on the
  coefficient field, log witnesses `u_j = W_j(x, y)/Q_j(x)` are **verified** (orders along the
  certified branches equal `m_j · coord_j(residue)`, no zeros or poles elsewhere by the norm), and
  the remainder `f − v′ − Σ (b_j/m_j) u_j′/u_j` is zero-tested.
  **`decideLog_spec`** (`ProcLogDecide.lean`): `decideLog ws = some b ⇒ (HasElementaryIntegral f ↔
  b)`; `some true` comes with the explicit Liouville form.
* **Automatic witnesses** `CurveProb.decideAuto P B Ew` (`ProcLogSearch.lean`): an untrusted
  Riemann–Roch-style linear-algebra search for the `u_j` (multiplier `≤ B`, `x`-degree `≤ Ew`),
  fed to `decideLog`; **`decideAuto_spec`** follows from `decideLog_spec`
  (`ProcLogAutoExample.lean`: both log examples below, witnesses found automatically).
* **Kernel-checked examples** (`decide +kernel`): `∫ √x/x` (`ProcRFExample`), `∫ dx/√(x(x−9)(x−25))`
  is not elementary (over `ℚ(i)`, `ProcRFExampleI`), `∫ dx/((x−1)√x)` is elementary with a
  logarithm (`ProcLogExample`), `∫ (1/y + 1/(x−9))` on `y² = x(x−9)(x−25)` is not elementary
  although its residue divisor is principal (`ProcLogExampleI`).
* **Non-torsion theory for general curves** (`Torsion/`, standard axioms only): the analogue of
  `SupTorsion`/`SupTwoPrimes` without cyclic covers. Functions are handled in integral-basis
  coordinates `∑ cⱼ(x) Bⱼ(x, y)/D(x)` (`LSpace.lean`: `IsIntBasis`, completeness of `L(M ∞ₓ)`);
  exact divisors from norms (`Exact.lean`, `ExactFn.lean`); the kernel of reduction has no
  prime-to-`p` torsion (`KernelField.lean`, `KernelDVR.lean`, `kernel_no_torsionG`); existence of
  the auxiliary function by counting (`Count.lean`, `Exist.lean`), its reduction (`Reduced.lean`,
  `DescendRed.lean`), its norm (`DescendNorm.lean`), the residual zeros by Hensel
  (`Residual.lean`), the `ℓ`-th power step (`EllPower.lean`); **`torsion_descendsG`**
  (`Descend.lean`): over a Henselian DVR, a class of order prime to `p` that is trivial modulo
  `p` is trivial. Then `principal_at_primeG` (`PrincipalMul.lean`), the linear-algebra
  principality test and its invariance under field extensions (`PrincTest.lean`,
  `principal_iff_test` in `PrincCurve.lean`), closure under `gcd` (`Gcd.lean`,
  `principal_two_primes`), and for divisors supported at points of unramified fibres
  (`Unram*.lean`, `PrimeStepUnram.lean`, `TwoPrimesUnram.lean`): **`not_torsion_unram`** — two
  good primes and a failed test for `(m_p m_q) Γ` over the base field prove that no multiple of
  `Γ − c ∞ₓ` is principal.
* **Certificates for non-torsion** (`Torsion/CertBasis*.lean`, `CertBranches.lean`,
  `TestCert.lean`, `ZpLift.lean`, `Eisenstein.lean`, `IntBasisCheck.lean`, `GoodPrime*.lean`,
  `NonTorsionCert.lean`, `NonTorsionMap.lean`): all characteristic-free. The pieces are:
  - integral bases from branch certificates (`isIntBasis_of_cert`, `ibCheck_spec`);
  - branch systems in characteristic `p` from certificates (`hasBranches_of_cert`);
  - the principality test from truncated expansions: a failed test via a left inverse
    (`not_princTest_of_cert`), a passing one via a kernel vector (`princTest_of_cert`);
  - lifting to `ℤ_p` (Hensel, `split_Zp`), and irreducibility over `ℚ_p(x)`, `𝔽_p(x)` and the
    coefficient field by Eisenstein at a point, by an irreducible specialization modulo `p`, or by
    the subset certificate (`irr_all`, `IrrSpec.lean`, `IrrSubset.lean`);
  - the non-speciality and determinant certificates, and reduction of the cover polynomial
    (`cover_red`).

  `hstep_of_prime` instantiates `prime_step_unram` at `O = ℤ_p` from `globalCheck` and
  `primeCheck` (`K` any computable field of characteristic `0` with a certified reduction
  `RedFns p K`). **`not_torsion_of_cert`** combines two primes with `nonPrincCheck`;
  **`not_torsion_of_cert_map`** transfers the result to every curve over an extension, such as
  the algebraically closed constants.
* **Möbius transformations** (`MobCurve.lean`): `mobCurve` (the curve `t = 1/(x − c)`,
  `w = y tᵏ` as a `CurveData` on the same field, via `invP`/`shiftP`); `mobCheck` (the
  transformed `CurveProb`, `f dx = f′ dt` with `f′ = −f/t²`); **`decideLogT_mob_spec`** (answers
  for the transformed problem are answers for the original one, via
  `hasElementaryIntegral_rescale_iff`).
* **Link to integrands** (`ResTors.lean`, `DecideLogT.lean`): `torsResCheck` identifies `s`
  times a component `coord j₀` of the residues with `Γ − c ∞ₓ` up to `div ∏ (x − a)^{e_a}`. The
  residues must be uniform along the certified branches at special points outside `Γ` and above
  infinity; this covers totally ramified points and a single place at infinity.
  **`false_of_torsRes`** shows that a Liouville form, via `curve_abel`, would make that divisor
  torsion. **`decideLogT_spec`** gives soundness of the extended decision.
* **Divisors at arbitrary places** (`RamPrime.lean`, `RamStep.lean`, `Curves/HenselR.lean`,
  `TestCertN.lean`, `RamRoots.lean`, `RamCert.lean`, `RamGood.lean`, `RamNonTors.lean`,
  `RamRes.lean`, `DecideLogP.lean`). The divisor `Γ` is given on the full branch systems
  `x = α_j + T^{N_j}`. The root `k` above `α_j` is the `ζ`-rotation of the `s`-reparametrization of
  the representative `ρ_π` of its place, with `N_j = s e_π`. `Γ` has multiplicity `s Γ_π` there.
  The pieces are:
  - `principal_at_prime_places` and `prime_step_places`: the prime step, with representatives
    over `O`;
  - `hensel_quantR`: Hensel over `O⟦T⟧`, `O` any commutative ring;
  - `rep_root_Zp`, `rep_match`: the representatives over `ℤ_p` from a `rootCheck` over the
    coefficient field whose leading derivative term is a unit modulo `p`;
  - `PlaceCert`: the certificate (`check`, `primeCheck`);
  - `hstep_places_of_prime`, **`not_torsion_places_of_cert`**, `not_torsion_places_map` (in
    `DivGE` form over any extension);
  - `torsResCheckP` and **`false_of_torsResP`**: the residues along the certified roots at
    places, with parameter `x = α_j + T^{N_j}`;
  - `decideLogTP` with **`decideLogTP_spec`**.
* **Kernel-checked examples**:
  - `TriExample.not_elementaryZ` (over `ℚ(ζ₁₂)`, standard axioms): the curve is
    `Y³ + 3xY − x² − 8x = 0` (genus `1`). The integral
    `∫ Y (c/(8(x + 16)) + 1/(12(x − 32))) dx` with `c² = −1` is **not elementary**. In its
    `c`-component the fibre `x = −16` has residue `−1` at the ramified place `(−16, −4)` (`e = 2`)
    and `+1` at the unramified place `(−16, 8)`, and the fibre `x = 32` has residues `0, 1, −1`.
    The witness uses primes `13` and `109` and an `18 × 12` failed test. It is checked by
    `torsOKP` in the kernel, split into eight lemmas (about 2 min in total, at most 9 GB each).
    `not_elementary_of_torsOKP` gives the statement. The certificates were generated by exact
    arithmetic (`scripts/tri_example/gen.py`).
  - `NonTorsionExample.nonTorsion`: on `y² = x (x + 27)(x − 48)` over `ℚ(i)`, `2 P − ∞ₓ` is not
    torsion for `P = (−24, 72)`, with primes `13`, `193` and a `12 × 12` failed test.
  - `DecideLogTExample.not_elementary`: `∫ 72 dx / ((x + 24) √(x (x + 27)(x − 48)))` is **not
    elementary**. `decideLog` alone returns `none`; `decideLogT` returns `some false` in the
    kernel (about 90 s).
  - `DecideLogTExample2.not_elementary2`: `∫ (72/((x + 24) y) + 1/(2x)) dx` on the same curve is
    not elementary. It has residues at the ramified point `(0, 0)` and above infinity; the
    divisor is `4P − 2∞ₓ` with scale `2`.
  - `MobExample.not_elementaryM`: `∫ x dx / √(x (x − 7)(x − 14)(x + 18))` is not elementary.
    Its residues are at the two places above infinity. The Möbius transformation at `x = 12`
    moves them to `(0, ±1)` of `w² = (1 + 12t)(1 + 5t)(1 − 2t)(1 + 30t)`, where `decideLogT`
    (primes `13` and `73`) answers `some false`.
* **Residues at points over a number field** (`BaseChange.lean`): `CurveProb.baseChange` moves an
  integrand to a larger coefficient field `F'` (for example a splitting field, `NFAdjoin`), with
  certificates over `F'`; **`decideLogTP_baseChange_spec`** decides the original integrand.
* **Computed prime data** (`AutoPrime.lean`): `autoPrimeCert` computes all the data at a prime
  (reduced integral-basis certificates with left inverses, base points, non-speciality
  coefficients, an irreducible specialization by `noSmallFactor`, otherwise the subset
  certificate at the first base point), `autoPlaceData` the multiplier
  `m_p` and its witness (smallest `m` with a kernel vector, `nullBasis`), `autoLm` the failed
  test over the coefficient field; `decideLogTPA` (sound by **`decideLogTPA_spec`**) needs only
  the global data and candidate primes. `TriAutoExample.not_elementaryZA`: the trigonal example
  with all prime data computed in the kernel (about 70 s).
* **Integral bases need not be triangular** (`LSpace.lean`, `CertBasisDet.lean`): `IsIntBasis` asks for
  `deg Bⱼ < n` and a non-zero determinant of the coefficient matrix (triangular bases are a special
  case, `det_of_tri`); `ibCheck` uses the determinant `detC` (by interpolation) in the cover
  polynomial, and the check above infinity is semantic (`basisCheckInfS`: true pole orders below
  the syntactic ones), so bases normal at infinity (Trager) are certified.
* **Simple discriminant roots need no certificate** (`Torsion/SimpleDisc.lean`,
  `IntBasisCheckR.lean`, characteristic `0`): if `Res_Y(F, F_Y)` vanishes to order `≤ 1` at `a`
  and `D(a) det [Bⱼ,ᵢ](a) ≠ 0`, the basis is locally independent along every Puiseux system above
  `a` (**`locIndep_of_mult_le_one`**: `∏ₖ f′(rₖ) = Res`, so `2 ord f′(rₖ) ≤ N`, and Lagrange
  interpolation at the `rₖ`; a Dedekind-type criterion; `isIntBasis_of_special_simple`).
  `ibCheckR` relaxes the cover condition of `ibCheck` to: the roots of `D · det` are certified
  points and the cover polynomial with the certified points stripped is separable (`sqfreeStrip`,
  `ibCheckR_spec`). The global certificate (`GlobalFacts.ib`, `globalCheckR`) uses the relaxed
  check; the prime checks (characteristic `p`) and the existence proofs keep the strict one
  (`globalCheck_ib`, `Char0Base.ibS`). This removes the need for rational branch points, which
  over a real field (e.g. `ℚ(x)`) cannot all carry rational ramified branches.
* **Computing the global data** (`Curves/AutoPuiseux.lean`, `Torsion/AutoIntBasis.lean`,
  `AutoPlace.lean`, `AutoPipeline.lean`; the number-field `Field` instance is computable, so
  everything runs natively):
  - `puiseuxAt`: Newton–Puiseux expansions (Newton polygons, edge polynomials, Newton's iteration),
    over a field with a root finder (`rfNF`, complete by `rootsIn_complete`, or `rfHint`, verified
    candidate roots); a missing root is reported as the polynomial to adjoin;
  - `autoIntBasis`: integral bases (local relations at the special points, normalization at
    infinity), checked by `ibCheck`;
  - `autoPlaceCert`: the place certificate of a residue component (places, residues, `Γ`);
  - `autoCurveProb`, `autoGlobal`, `autoTorsWits`, `decideAutoP` (sound by **`decideAutoP_spec`**);
  - `decideAutoPM` (`AutoMob.lean`): the same after a Möbius transformation `t = 1/(x − e)`, so
    that non-uniform residues above infinity become residues at a finite fibre (sound by
    **`decideAutoPM_spec`**, via `decideLogTP_mob_spec`);
  - `decideAutoFull` (`AutoLog.lean`): for each residue coordinate, either the test at
    `m_p m_q Γ` passes over the coefficient field and its kernel vector gives a log witness
    (`logWitOf`), or the non-torsion witness is computed (sound by **`decideAutoFull_spec`**);
  - `decideLoop` (`AutoField.lean`): for an integrand over `ℚ`, the whole decision over number
    fields `ℚ[γ]/(M)`, adjoining a root (`extStep`, Trager's primitive element) whenever a
    polynomial needed by the pipeline does not split (`probeMissing`), with the complete root
    finder `rfNF`; **`decideLoop_spec`**: every answer is correct.
  - `NullTest.lean`, `KernelComplete.lean`: the kernel search is complete — if `testKernel` finds
    no relation (`nullBasis` of the test columns `kerCols` is empty), the principality test fails
    over every extension of the coefficient field (**`not_princTest_of_nullN`**, via
    `nullBasis_complete`). The failed-test certificate of the non-torsion witnesses is now
    `nonPrincOK`: a left inverse (`nonPrincCheckN`) **or** an empty null space recomputed by the
    checker (`not_princTest_of_nonPrincOK`), so it passes whenever the kernel search fails
    (`nonPrincOK_of_testKernel`).
  - **Front end** (`Torsion/Front.lean`): `decideCurveQ Fc A D` decides `∫ A(x, y)/D(x) dx` on
    `F(x, y) = 0` over `ℚ` with no other input — the weights at infinity (`autoK`, `autoKI`), the
    number fields (`decideLoop`), the primes (`autoPairs`: the first primes at which the field has a
    certified reduction) and the precisions are chosen automatically; **`decideCurveQ_spec`**: every
    answer is correct. `emitCurveQ` writes the kernel-checkable certificate file for the answer.
  - **`TriQExample.not_elementary`** (`Torsion/TriQExample.lean`): the first theorem produced end
    to end by the pipeline. On `Y³ + 3xY − x² − 8x = 0`, `∫ Y (4/3 + x/12)/(x² − 16x − 512) dx`
    (rational coefficients) is **not elementary**. `decideLoop` built `ℚ(ζ₁₂)` itself (adjoining `i`,
    then a root of `Y³ − 8` over `ℚ(i)`), and the branch data, the place certificate of one residue
    coordinate, the prime data at `13` and `37` (`m₁₃ = 3`, `m₃₇ = 2`, test at `pairMult = 1`) and the
    failed test were computed natively; `emitNonElem` printed the file, which the kernel checks in
    about 5 minutes (10 GB). Two other coordinates need tests with `c_Γ = 25` and much higher
    precision; one non-torsion coordinate suffices, so `decideAutoFull` now treats the cheap
    coordinates first and stops at the first passing witness.
  - **`EllElemExample.elementary`** (`Torsion/EllElemExample.lean`): the elementary side, end to
    end. `∫ √(x³ + 1)/x dx` on `y² = x³ + 1` is **elementary**: `emitLoop` built `ℚ(ζ₁₂)`, found the
    order `3` of the residue divisor `(0, 1) − (0, −1)` by the kernel search of the principality
    test (primes `13`, `37`), the logarithm `u = W/Q` (`logWitOf`) and the exact part, retrying the
    branch data with more precision (`exs`) until the witness is visible; `emitLog` printed the
    file, checked by the kernel in about 3 minutes (14 GB).
  - `Emit.lean`: **certificate emission** — `emitStage` reruns the last stage of `decideLoop`
    natively over the field it found and prints a Lean file with the certificates behind the
    answer (the branch data of the integrand, and either the log witnesses or a non-torsion
    witness at places), one `decide +kernel` lemma per conjunct of the check, and the theorem for
    the integrand over `ℚ` (`not_elementary`, via `not_elementary_of_torsOKP`, or `decided`, via
    `decideLogTP_baseChange_spec`) — the same shape as `TriExample`, but generated. `emitLoop`
    runs the field loop first (one call from the integrand over `ℚ` to the certificate file); the
    branches above infinity are checked one root at a time (`emitInf`). The emitted
    file is ordinary Lean and is checked by the kernel; nothing in the emitter is trusted.
  - kernel cost of the branch certificates: `rootCheck` evaluates `F(a + Tᴺ, ỹ)` by a Horner
    scheme truncated at the needed precision (`bivEvalT`); `rootCheck_facts` shows that it implies
    the exact check (`rootCheckFull`), so every certificate check keeps its semantics while the
    kernel no longer builds the full composed polynomial (for a branch certificate above infinity
    with `N = 3`, precision 62 and coefficients of size `10²⁰`, the exact check exceeded 16 GB).
  - `NFRootsZ.lean`: a fast root finder `rfNFZ` in number fields — Trager's norm method with an
    (unverified) Zassenhaus factorization over `ℤ` (`ZF.factorZ`: distinct/equal-degree
    factorization modulo `p`, multifactor Hensel lifting, recombination) instead of Kronecker's
    exponential search; its answers are checked by multiplicities exactly like `rfNF`, and every
    use of a root finder is re-certified (`certCheck`), so no proof is needed (a degree-20 norm over
    `ℚ(ζ₁₂)` is split in well under a second). `decideLoop fast …` uses it with `fast = true`,
    and retries the certificates of the integrand with the extra precisions `exs`.

  Only the input curve, integrand, candidate primes and search bounds are supplied. Completeness
  of these searches (`≠ none` for large bounds) is **not** proved: it needs the termination of the
  Newton–Puiseux and integral-basis loops, the finiteness of the extension loop, and the existence
  of good primes with split base points (Chebotarev / Weil-type statements not in Mathlib, or
  global base points over an extended field reduced modulo large primes); irreducibility modulo
  `p` no longer needs an irreducible specialization (subset certificate). The principality test
  from truncated expansions allows the integral-basis denominator to vanish at the support of the
  residue divisor (residues above singular fibres of the model): with `μⱼ` the order of
  `D(αⱼ + Tᴺ)`, `Bᵢ/D = T^{−μⱼ} V` along the branch (`basisSer_truncN`), the rows of the test are the
  coefficients `t < bⱼₖ + μⱼ` of `V` (`rowsN`, `test_rowsN`, `test_negN`), and `testSideN` only
  asks `bⱼₖ + μⱼ ≤ prec`. In practice `rfNF` (Kronecker factorization of norms) is too slow
  beyond small degrees; `rfHint` (verified candidate roots) is used for runs, e.g. the trigonal
  example is recomputed natively in about 12 minutes.
* **Torsion dichotomy** (`torsion_iff_test_places`): with the prime steps at `p` and `q`, some
  multiple of `Γ − c ∞ₓ` passes the principality test iff `m_p m_q` does. The multiplier can be
  lowered to any `mt` divisible by every `gcd(m_p pᵛ, m_q q^w)` (`principal_two_primes_mt`,
  `not_torsion_places_mt`), in particular to `pairMult p q m_p m_q = gcd(m_p p^E, m_q q^E)`
  (`PairMult.lean`, `dvd_pairMult`; e.g. `m₁₃ = 3`, `m₃₇ = 2` give `1` instead of `6`), which keeps
  the linear system over the coefficient field small; `torsOKP` accepts a failed test at `m_p m_q`
  or at `pairMult`, and the automatic path uses `pairMult`. The multipliers `m_p` are searched up
  to `max B (√p + 2)^{2g}` (`hwBound`, a Hasse–Weil-type bound; only a search bound).
* **Finiteness of `Pic⁰` over finite fields, general curves** (`PicTorsion*.lean`, the existence of
  the multipliers `m_p` behind every non-torsion certificate). **`exists_principal_mul`**: over a
  finite field, if for every `M` some `u_M ≠ 0` has `div u_M ≥ M Γ − (M c + s) ∞ₓ` (Riemann's
  inequality), then some multiple `m (Γ − c ∞ₓ)` is principal. The proof stays in the explicit
  branch model: the surplus of `u_M` over `M Γ − (M c + s) ∞ₓ` has total `n s` by the degree theorem
  (`fibre_sum`, `inf_sum`, `surplus_total`); off `Γ` it lies above points `b` with
  `μ(b) = mult_b N(W) − n mult_b Q > 0`, and since the Frobenius `b ↦ b^q` preserves root
  multiplicities of polynomials over `𝔽_q` (`rootMult_frob`), these points satisfy
  `b^{q^{(ns)!}} = b` (`support_fixed`) — finitely many; a pigeonhole on the bounded surplus vectors
  gives `M₁ < M₂` with equal surpluses, and `u_{M₂}/u_{M₁}` has divisor exactly
  `(M₂ − M₁)(Γ − c ∞ₓ)` (order transfer between branch systems at finite points and at infinity).
  **`riemann_unram`**: at unramified places the test has more unknowns than conditions
  (`princTest_of_card_lt`); hence **`exists_principal_test_unram`**: for divisors supported at
  unramified points, some multiple passes the principality test. **`riemann_places`** handles
  arbitrary (ramified) places: conditions are imposed only along one representative root
  `lsub s ρ_π` per place, and the orders along its conjugates `rot ζ (lsub s ρ_π)` are `s` times
  those along it, so the count is again unknowns > conditions; hence
  **`exists_principal_test_places`**: for any degree-`0` divisor over a finite field (given the
  branch data), some multiple `m` passes the test — the multiplier `m_p` always exists
  mathematically. **The search finds it** (`PlaceWitSpec.lean`, `PlaceComplete.lean`):
  `placeWit` now returns a *non-zero* relation of the test columns, and `placeWit_spec` proves
  that it always passes `princWitCheckN`. `placeWit_isSome` proves that the search succeeds
  whenever the test holds over some extension and the precision suffices (via
  `nullBasis_complete`). **`exists_autoPlaceData`**: at a prime passing `PrimeFacts` and the
  checks of `primeCheck` that do not involve `m_p` (`primePre`), there is `m_p ≥ 1` such that
  for every bound `B ≥ m_p` with enough fibre precision at `m_p` (`testSideN`), `autoPlaceData`
  returns data accepted by `primeCheck`. The proof applies `exists_principal_test_places` to
  the reduced curve over `𝕜 ≅ 𝔽_p`. **`autoPlaceData_spec`**: whatever it returns is
  accepted. Two properties of the place data are now checked by `PlaceCert.check`: every place
  carries a root, and `∑ Γ_π = c n`. **`exists_autoPlaceData_tp`** states the precision
  condition on the bound alone: `B s Γ_π ≤ tp_j`, using `testSideN_of_tp` (`D(α_j) ≢ 0` gives
  `μ_j = 0`). `autoCoord` now ends its precision doubling with `tp = B′² · need + 2`, which
  satisfies this condition for every multiplier up to `B′²`, including `pairMult`. It remains
  open that the place search produces correct data at that precision, and that `primePre` and
  `PrimeFacts` hold at some prime.
* **A total decision** (`Torsion/DecideEnum.lean`, completeness in `Torsion/CertExistsFinal.lean`).
  `decideTotal Fc A D N` runs the pipeline `decideCurveQ` first. If that fails, it tries the
  first `N` of **all** certificates `(M, pts, inf, ws, twps)`, i.e. a number field
  `ℚ[γ]/(M)`, branch data, logarithmic and non-torsion witnesses, enumerated through
  `Encodable` instances. Each is checked with the sound `decideLogTP`.
  * `decideTotal_spec`: every answer is correct.
  * `decideTotal_complete`: if valid certificates exist (`CertExists`), the decision answers for
    every large `N`.

  This moves completeness away from the heuristic searches (Newton–Puiseux recursion,
  integral-basis loop, extension loop, prime search) to **existence theorems** for
  certificates. **`CertExists` is now proved for every problem over `ℚ` with valid shape whose
  curve exists** (`certExists_of_curve`), so:
  * **`decideTotal_complete_curve`**: `decideTotal` answers for every large `N`;
  * **`decideTotal_decides`**: for every large `N`, `decideTotal Fc A D N = some b` and
    `HasElementaryIntegral (A/D) ↔ b = true` (standard axioms only).

  The proof of `certExists_of_curve`:
  * a Möbius transformation `t = 1/(x − e)` at a rational `e` with `D(e) ≠ 0` moves the fibre
    above infinity to a regular point. The transformed problem has valid shape
    (`mobT_shapeOK`; `mobCheck`/`mobT` now trim the transformed numerator's coefficients,
    `mobA`), and all its residues above infinity vanish (`resInf_mob_eq_zero`,
    `Torsion/MobInf.lean`: the integrand becomes `−T^{2N} A/D` with `y` integral over `K⟦T⟧`,
    `orderTop_nonneg_of_monic_root`);
  * for such problems (`certExistsN_of_inf0`, `Torsion/NonTorsFinal.lean`), a first number field
    and integral basis give non-special base fibres over the constants with integer abscissas and
    algebraic ordinates (`exists_basepointsR`, `exists_QB_pre`); a number field containing them,
    the branch data and the roots of unity follows (`exists_valid_ext`). If every residue
    coordinate is torsion, logarithmic witnesses exist (`certExistsN_of_tors`). Otherwise the
    genus is positive (`genus_pos_of_nonTors`, Riemann's inequality for the places), and a
    non-torsion witness accepted by `torsOKP` exists (`exists_torsOKP_of_base`: global
    certificate, base-point data, place checks at all large primes with one `m_p` for all
    precisions, `hbase_of_C`);
  * certificates of the transformed problem give certificates of the original one with the
    Möbius option (`certExists_of_mobN`).

  The ingredients (all proved) were:
  * Puiseux data over a number field (`puiseux_split` plus `rootCheck_of_root`);
  * integral-basis certificates;
  * good primes (Schur);
  * `m_p` (`exists_placeWit`, done);
  * failed tests (`nonPrincOK_of_testKernel`);
  * logarithmic witnesses in the torsion case (done, see below).

  Existence pieces done so far:
  * `NFC.exists_nf` (`Algebraic/NFExists.lean`): any finite set of algebraic numbers lies in
    the image of a computable number field `NF M → ℚ̄` with `Kron.irredQ M = true`, via a
    primitive element, an integral multiple and `irredQ_complete`.
  * `exists_branchCert` (`Torsion/CertExistPt.lean`): at every point of a separable monic curve,
    and for every large precision, there are branch certificates passing `certCheck` over every
    coefficient field that reaches the point and the finitely many Puiseux coefficients involved.
    The proof uses `puiseux_split`, a Bézout identity for simple roots, and `rootCheck_of_root`.
  * `coverCheck_complete` (`Curves/CoverComplete.lean`): the cover check is exact.
  * `shapeOK_baseChange`, `valid_of_shapeOK` (`Torsion/ValidBase.lean`): the problem-level
    conditions of `valid` survive base change (`discRC` through its meaning as a resultant).
  * **`exists_valid`** (`Torsion/ValidExist.lean`): for every problem over `ℚ` with valid shape,
    separable at the finite fibres and at infinity (Bézout identities), valid branch data exist
    over some certified number field. They are placed at all roots of `D · disc` and at infinity,
    at precisions above the orders of `R0` and `D`.
  * **`certExists_or_residues`**, **`decideTotal_complete_or_residues`**
    (`Torsion/CertExists.lean`). Separability at the finite fibres follows from `shapeOK`
    (`hsep_of_shapeOK`, via Mathlib's `exists_mul_add_mul_eq_C_resultant`), and so does
    separability at infinity (`Torsion/SepInf.lean`: `resultant_invB_ne_zero`, from
    `F̃(t, tᵏY) = t^{kn} F(t⁻¹, Y)` over Laurent series and invariance of separability under
    `Y ↦ cY`; `hsepI_of_shapeOK`). So for every problem with valid shape, either `decideTotal` answers for every large
    bound, or the integrand has a logarithmic part. In that case valid data exist for which the
    linear system is solvable and the residues do not all vanish. **So the total decision is
    proved complete for every integrand without a logarithmic part.**
  * **Logarithmic witnesses in the torsion case** (`Torsion/LogWitB.lean`,
    `Torsion/CertExistsTors.lean`, standard axioms). For a curve over any constant field `C` of
    characteristic 0 with branches over an algebraically closed `K ⊇ C`, a torsion residue
    coordinate (`TorsOrd`: some `w ≠ 0` has order `m · Λ(res f dx)` along every branch,
    `Λ ∘ ψ₀ = coord_j`) yields a witness `⟨m, W, Q⟩` accepted by `witOK` (`witOK_of_tors`):
    `w = W₁/Q` with `Q` over `F` (`exists_W1`, from `exists_repr_poles`), linear descent of `W₁`
    to `F` along the exact certified branches (`exists_WF`, `fin_roots_F`, `inf_roots_F`),
    exactness of the orders and of the norm (`exact_at`, from `exact_divisor`), and a precision
    bound met by `raise_valid` (which now keeps the ramification indices). Then
    `witCheck_of_tors`, `certExists_of_tors`, and:
    * **`certExists_of_elementary`**: valid certificates exist for **every elementary
      integrand** (torsion from `curve_lift`, `liouville_C`, `curve_abel` over the algebraic
      closure of the constants of the Liouvillian extension);
    * **`decideTotal_complete_of_elementary`**: the total decision answers (`true`) for every
      elementary integrand with valid shape;
    * **`certExists_or_nonTorsion`**: in general, valid certificates exist unless some residue
      coordinate has a non-torsion residue divisor. That case is now also covered
      (`certExists_of_curve`, above).
  * **Certified integral bases exist** (`Curves/Restrict.lean`, `Torsion/IBExist1..8.lean`,
    standard axioms). `CurveData.restrict` views the curve over the certificate field `F`.
    Over `F` itself (branch systems with exact roots in `F⟦T⟧` from the certificates), Trager's
    construction is carried out: improvement at the special points while the reductions modulo
    `x − a` are dependent (`stepB`; the local index `mult_a(discⁿ det B) − n mult_a D`, a natural
    number by the Cramer bound `index_bound`, drops by one), then reduction at infinity while the
    leading terms are dependent (`stepI`; `∑ δⱼ` drops). No integral function vanishes at infinity
    (`evXY_eq_zero_of_vanish`, by norms and a degree count), which also gives `δⱼ ≥ 1` for
    `j ≥ 1`. **`exists_basis`** yields a normalized integral basis; the checks accept it
    (`basisCheckAt_complete`, `basisCheckInfS_complete`: vanishing conditions from regularity, left
    inverses from independence, `exists_leftInvCheck`), after raising the precision
    (`raise_certCheck` with transfer between branch systems). **`exists_ibCert`**: an
    `IntBasisCert` passing `ibCheck` (with `GlobalCert.G`) and `normCheck`, with monic denominator,
    exists at any certified distinct points covering the discriminant.
  * **The residue theorem** (`Torsion/ResThm1..3.lean`, standard axioms): on the line for rational
    functions with split denominator (`sum_res_eq_zero`, by peeling off roots), and on the curve
    (**`curve_res_sum`**): for `f = W(x, y)/Q(x)` the residues along complete branch systems above
    the roots of `Q` and above infinity, divided by the ramification indices, add up to `0`. The
    fibre sums are the residues of the trace `Tr W = [t] Res_Y(F, 1 + tW)` (`map_trW`).
  * **Places** (`Torsion/PlaceExist1..3.lean`): the roots `yₖ(T)` of `F(a + Tᴺ, Y)` are permuted by
    `T ↦ ζT`; the orbits are the places, with ramification the minimal period `e` (dividing `N`,
    `∑ e = n`), each root being `ρ((ζⁱT)^{N/e})` for a place series `ρ` at level `e`; residues along
    a place's roots are `N/e` times the residue along `ρ` (`res_conj_place`).
  * The exhaustive fallback `decideEnum` now also enumerates Möbius transformations
    `t = 1/(x − e)` (`CurveProb.mobT`, checked by `mobCheck`), needed so that the fibre above
    infinity can be made regular for the non-torsion certificates.
  * Tools proved for the torsion case:
    * `exists_kernel_of_ext` (`Torsion/LinDescent.lean`): linear descent of kernels from an
      extension field.
    * `raise_certCheck` (`Torsion/RaisePrec.lean`): raising the precision of branch data over
      the same field.
    * `discr_eq_resultant` (`Curves/DiscrRes.lean`): the power-basis discriminant is
      `± Res(f, f′)`, with the resultant as a product over roots, `resultant_eq_prod_eval`.
    * `res_mul_integral` (`Curves/ResIntegral.lean`): `Res(F, F_Y) · z ∈ C[x][y]` for every
      integral function `z`.
* **Completeness of the branch computations** (first pieces): `rootCheck_of_root`
  (`Torsion/RootCheckComplete.lean`) shows the root check accepts every approximation of a true
  root `ρ` to precision `ord F_Y(ρ) + prec`. `newtonT_root` / `exists_newtonT_root`
  (`Curves/NewtonT.lean`) show the truncated Newton iteration used by `puiseuxAt`, `npRec` and
  `liftRootsAt` is correct. For a simple root, `log₂ L + 3` steps of `newtonT` agree with the
  Hensel root modulo `T^L`. The proof is quadratic convergence (`newton_step`) with the exact
  semantics of the truncated arithmetic (`evalBT_getD`, `sMulT_getD`). The Newton-polygon
  recursion itself (`npRec`: termination and completeness of the branches) is not yet proved.
* **Not proved for the practical pipeline**: `decideTotal` is proved complete through its
  exhaustive certificate enumeration (above), which is a decidability proof, not a usable search.
  For the automatic pipeline `decideCurveQ` / `emitCurveQ` that computes the global data (branch
  expansions with the needed algebraic extensions, integral bases, place certificates, prime
  data), **completeness is not proved**: that
  every search succeeds for large bounds (termination of the Newton–Puiseux and integral-basis
  loops, finiteness of the extension loop, existence of good primes with split base points —
  e.g. from global base points over an extended field — and that the precision of the place data
  is raised enough for the multiplier `m_p`, which the search is now proved to find
  (`exists_autoPlaceData`)). In practice the searches are also limited by
  cost: native runs take minutes to an hour on genus-1 examples over quartic fields, the kernel
  checks of the emitted certificates take minutes and 10–16 GB, and residue coordinates whose
  divisor has a large degree `c_Γ` need tests with many rows (reducing the divisor first is not
  done).

Details of what is and is not treated in each area:

* height three: all towers of two primitives are treated except a nested primitive whose
  residues are constants but which is not a logarithm of an element of the field (`W = 2 u′/u`
  after a change of constants, or `W = u′/u + w′`; the algorithm would first normalise `t₂`);
  an exponential on top of a primitive tower (`Tower.integrateExpPrim`), two exponentials
  (`Tower.integrateExpExp`), a logarithm on top of an exponential tower
  (`Tower.integratePrimExp`) and a non-elementary primitive on top of an exponential tower
  (`Tower.integrateLiExp`) are done; as for two primitives, a primitive `t₂` over `R(x)(eˣ)`
  whose residues are constants but which is not a logarithm of an element of the field is
  not treated (the algorithm would first normalise `t₂`);
* towers of general height: **towers of any number of primitives over `ℚ(x)`** (`tₘ′ = ηₘ ∈ ℚ(x)`)
  are decided (`Tower.PrimN.PrimTower.primN_decides`, `Computable/PrimN*.lean`): the tower lives in
  one differential field `E`, each level `F m = Kc(x, t₀, …, t_{m-1})` is an intermediate field
  with a model of the codes (`CField.monomialVia`), parametric limited integration `limIntP` is
  proved sound and complete (with arbitrary constants) at every level by induction, the
  independence certificate `primCert` (each `ηₘ` has no antiderivative in `F m`) makes every
  `tₘ` transcendental with no new constants (`nd_of_primCert`), and `elemP` is sound
  (`HasElementaryIntegralIn`) and complete (from a Liouville form up to `Kc(x)`, using the new
  `Differential.poly_part_liouville`, `Liouville/PrimitivePolyPart.lean`). **Mixed towers of any
  height** of primitives `tₘ′ = ηₘ ∈ ℚ(x)` and (hyper)exponentials `tₘ′ = bₘ tₘ`, `bₘ ∈ ℚ(x)`, are
  decided too (`Tower.MixN.MixTower.mixN_decides`, `Computable/MixN*.lean`): the Risch
  differential equation `y′ + f y = A` is solved at every level (`rdeM`: `y = Y / D`, no new
  poles, top-degree recursion; at the base the weakly normalised solver `rdeRationalW`; sound and
  complete, uniqueness from `LogIndep`: no non-zero `ℚ`-combination of the exponents is a
  logarithmic derivative in `Kc(x)`, `MixNLog.lean`. `LogIndep` is certified by `logIndepCert`:
  either all exponents are derivatives in `ℚ(x)` (`derivCert`, then `deriv_eq_zero_of_add_proper_eq_logDeriv`),
  or `hermKernelCert` (`MixN.lean`, soundness `logIndep_of_hermKernelCert` in `MixNHexp.lean`):
  a relation `∑ cⱼ bⱼ = e′/e` forces a relation among the Hermite parts and integer residues;
  the relations among the Hermite numerators are computed by elimination (`KerElim.lean`), and
  the residue combinations of a relation space of dimension ≤ 2 are refuted by `nonRatVals` or the
  pair certificate `degenCertQ` (`degenCertQ_sound`); relation spaces of **any dimension** are
  refuted by factoring the squarefree denominator `s` over `ℚ` (Kronecker's method,
  `Computable/Kronecker.lean`: every factor is certified irreducible, `irredQ_sound`, via Gauss's
  lemma and uniqueness of interpolation) and checking that no non-zero combination of the residue
  polynomials is constant modulo every irreducible factor (a linear system over `ℚ`;
  `genResCert_sound`, `Computable/KronCert.lean`; example with three hyperexponentials
  `exp ∫ dx/(x² - k)`, `k = 2, 3, 5`, in `Computable/MixNExample3.lean`). `notSpanCert` (numerators over a common denominator,
  `linSolve`) certifies `ℚ`-independence; both proved sound in `MixNComplete2.lean`), limited integration handles exponential levels through their
  Laurent coefficients, and the Laurent part of a Liouville identity in an exponential extension
  is characterised by `Differential.laurent_part_liouville` (`Liouville/ExponentialLaurentPart.lean`).
  **Towers of primitives with nested data at any height** (`tₘ′ = ηₘ ∈ F m = Kc(x, t₀, …, t_{m-1})`:
  `log x`, `log log x`, `li`-type primitives, …) are decided too
  (`Tower.NestP.NestTower.nestN_decides`, `Computable/NestP*.lean`). The key tool is **parametric**
  integration with parameters at every level, proved sound (rational parameters) and complete
  (arbitrary constant parameters) by induction on the level: parametric limited integration
  `paramLim` (`y′ = ∑ cᵢ wᵢ`; `paramLim_spec`, `NestPParamStep.lean`: Hermite reduction of every
  weight, the simple parts cancel — a linear system over the constants, solved exactly by
  `consys`/`nullBasis` — and the polynomial parts give the parametric polynomial problem
  `paramPoly`, `NestPPoly.lean`, whose degree loop calls `paramLim` one level down), and
  parametric elementary integration `paramElem` (`∑ cᵢ wᵢ` has a Liouville form over `F m`;
  `paramElem_spec`, `NestPElem.lean`): the Hermite remainders are put over their lcm `S`
  (checked squarefree, and proved always to pass), the residue test `S ∣ T(∑ cᵢ Rᵢ, S)` is linear
  in `c` (`residueTest_sum`) and becomes a constant system at level `m + 1`
  (sufficiency: `hasElementaryIntegralIn_of_residueTest`; necessity:
  `residueTest_step_primitive`), and the polynomial part is the parametric elementary polynomial
  problem `polyElem` (`NestPElemPoly.lean`: the degree loop down to degree 1, then `paramElem`
  one level down on the degree-0 equation; completeness from `poly_part_liouville`). The
  certificate `nestCert` (each `ηₘ` has no antiderivative in `F m`, read off the `paramLim`
  basis) gives transcendence and no new constants (`nd_of_nestCert`). Kernel-checked examples
  (`Computable/NestPExample.lean`): `∫ dx / log x` and `∫ log log x dx` are not elementary;
  `∫ dx/(x log x)`, `∫ log log x/(x log x) dx` and `∫ (log log x + 1/log x) dx = x log log x`
  are. **Towers of exponentials with nested arguments at any height** (`tₘ = exp aₘ`,
  `aₘ ∈ F m`: `eˣ`, `exp(eˣ)`, `e^{x²}`, …) are decided as well
  (`Tower.NestM.NestMTower.nestM_decides`, `Computable/NestM*.lean`). Here the key new tool is
  the **parametric Risch differential equation** `y′ + h′ y = ∑ cᵢ wᵢ` at every level (`prde`,
  proved sound and complete over the constants by induction: `prde_spec`, `NestMRdeExpC.lean`):
  at the base a linear system after a uniform degree bound (`NestMRde0.lean`); at an exponential
  level the normal denominator bound `gcd(e, e′)` (`RDE/NestedBounds.lean`, `rde_pole_bound`),
  the special bound at `t = 0` from the structure theorem (`Z′ = u′/u` forces
  `Z = ∑ qᵢ aᵢ + κ`, `exp_structure`, `Liouville/ExpLogDerivStructure.lean`; `pld_spec`), the
  degree bound with the balanced case through values at infinity (`RDE/ValInf.lean`, `pe_Nb`),
  the top-down coefficient loop calling `prde` one level down (`NestMRdeLoop.lean`,
  `rdeLoop_stage`) and a final constant system (`peOut_complete`). Parametric limited
  integration (`paramLimM_spec`, `NestMLim.lean`) splits every weight as
  `g′ + r/s + L/tᵏ` (`exp_weight_decomp`), cancels the normal simple parts
  (`deriv_eq_laurent_add_sum_proper`, `Liouville/ExpProperSum.lean`) and solves the Laurent
  coefficients with the same loop (`A = 1`, `B = -S a′`; the constant coefficient by `paramLimM`
  one level down). Parametric elementary integration (`paramElemM_spec`, `NestMElem.lean`): the
  residue test over the lcm of the simple parts (necessity `residueTest_step_exponential`,
  sufficiency `hasElementaryIntegralIn_of_residueTest` with `θ = t`), and a coefficient loop
  (`elemLoop_stage`) requiring a solvable Risch equation `y′ + (j - S) a′ y = Pⱼ` for each Laurent
  coefficient `j ≠ S` and an elementary integral one level down for `P_S` (necessity:
  `exp_liouville_split`, from `laurent_part_liouville` and `laurent_coeff_eqs`). The certificate
  `expCertM` gives transcendence of every `exp aₘ` (`tr_of_expCert`).
* **mixed towers of logarithms and exponentials with nested data** (`Computable/NestX*.lean`,
  decision theorem `nestX_decides` in `NestXDecide.lean`): the Risch equations arising in such
  towers have coefficients `f = h′ + ∑ cⱼ wⱼ′/wⱼ` (constant `cⱼ`), a class closed under the
  recursion (`FRep`). The structure theorem `mix_structure` (`NestXStructure.lean`: `Z′ = ∑ cₖ uₖ′/uₖ`
  forces `Z` to be a constant combination of the `tᵢ` (logarithms) and `aᵢ` (exponentials)) gives
  the logarithmic-derivative bound `pldX` (`pldX_spec`) and certificate soundness
  (`mixHyp_succ`, `NestXCert.lean`). Normal denominators `gcd(e, e′)·Lᴺ` come from the residue
  bound `rde_log_denominator` (`RDE/LogBounds.lean`: a pole of `y` beyond that of `g` has order
  `k = ∑ cⱼ ordₚ wⱼ`, bounded by `logBound` via rational recognition `ratVal_spec`); the special
  bound at `t` (`rde_special_bound_reg_R`/`_pole_R`) and the degree bounds use `pldX` at exponential
  levels and limited integration (`limN`, with `η` not a derivative) at logarithmic levels, where
  the balanced case recurses on `f = h₁ vₘ′/vₘ + h₀′ + ∑ cⱼ lc(wⱼ)′/lc(wⱼ)`. Proofs:
  `prde0X_spec` (`NestXRde0.lean`), `prdeExpX_spec` (`NestXRdeE*.lean`), `prdePrimX_spec`
  (`NestXRdeP*.lean`), `expLimStepX_spec`/`expElemStepX_spec` (`NestXLimE.lean`,
  `NestXElemE.lean`), `primLimStep_spec`/`primElemStep_spec` (`NestXLimP.lean`,
  `NestXElemP.lean`), assembled by simultaneous induction (`xspecs`);
* hyperexponentials `t′ = η t` whose `η` has simple poles are done at height two
  (`Tower.integrateHyperexpW`) and inside two height-three towers (`hexpPrim`, `primHexp`). For a general hyperexponential `t₂` over a primitive
  `t₁`, the RDE (`Tower.rdePrimW`) and the negative theorems for the Laurent part and the residue
  test (`CPoly.not_elementary_hexpPrimLaurent`, `CPoly.not_elementary_hexpPrimResidue`) are
  proved, and the whole tower is decided by `Tower.integrateHexpPrim` (the term `c₀ η` left by
  Liouville's exponential step is absorbed as one more logarithmic term `(c₀ η x) x′/x` of the
  primitive step; kernel-checked examples in `Computable/IntegrateHexpPrimExample.lean`:
  `∫ exp (arctan x) log x dx` is not elementary, `∫ exp (arctan x) (1/x + log x/(x²+1)) dx` is).
  A logarithm over a general hyperexponential (`t₂ = log U`, `U ∈ R(x)(t₁)`, `t₁′ = η t₁`) is
  decided by `Tower.integratePrimHexp` (`Computable/IntegratePrimHexp.lean`; examples in
  `Computable/IntegratePrimHexpExample.lean`); a non-elementary primitive over it by
  `Tower.integrateLiHexp` (`Computable/IntegrateLiHexp.lean`); an exponential `exp a(x)` over it by
  `Tower.integrateExpHexp` (`Computable/IntegrateExpHexp.lean`; the Risch differential equation
  over `R(x)(t₁)` with coefficients `g + z η`, `Computable/RDEHexp.lean`, is solved by the weakly
  normalised solver; independence certificate `CPoly.hexpExpIndep`, `Computable/HexpExpIndep.lean`).
  Two general hyperexponentials are decided by `Tower.integrateHexpHexp`
  (`Computable/IntegrateHexpHexp.lean`; RDE with rational coefficient `Computable/RDEHexp2.lean`,
  residue annihilators computed by `findMu`; independence certificate
  `CPoly.hexpHexpIndepFull`, `Computable/HexpHexpIndep.lean` and `HexpHexpIndep2.lean`: the
  coprime-denominator certificate, or — for shared poles — the Hermite-part certificate
  `hexpHexpComb`: `zη₁ + cη₂ = e′/e` forces `z η₁ᴴ + c η₂ᴴ = 0`, which is impossible, or fixes
  `z/c` and then requires `k η₁ + η₂` to have only rational residues. The remaining **degenerate pairs** — both `ηᵢ`
  with only simple poles and no polynomial part, sharing poles — are certified by `CPoly.hexpDegen`
  (`Computable/HexpDegenerate.lean`, soundness `CPoly.hexpDegen_hom` in
  `HexpDegenerateSpec.lean`): over a common squarefree denominator `s` the residue polynomials
  `ρᵢ` are computed; `z η₁ + c η₂ = e′/e` forces `λ ρ₁ + ρ₂` (`λ = z/c`) to take only rational
  values modulo the primes of `s` over any constant field (`Differential.residue_int_of_logDeriv`);
  a verified polynomial identity `D(Λ) ρ₁ ≡ ∑ gⱼ(Λ) (Λ ρ₁ + ρ₂)ʲ (mod s)` (found by
  fraction-free elimination over `ℚ[Λ]`, checked coefficientwise) confines `λ` to the rational
  roots of `D`, each of which is refuted by a non-rational residue value. The combined
  certificate is `CPoly.hexpHexpIndepAll`, used by `Tower.integrateHexpHexp`; kernel-checked
  example with `η₁ = 6/(x³-2)`, `η₂ = 6x/(x³-2)` in
  `Computable/IntegrateHexpDegenerateExample.lean`. `hexpDegen` also accepts the **head
  certificate** `Kron.genResCertHead s [ρ₂, ρ₁]` (`Computable/KronHead.lean`): `s` is factored by
  Kronecker's method and every null-space vector of the non-constant remainder coefficients of
  `ρ₂, ρ₁` modulo the factors must have first entry `0`. This check is **proved exact**. It is
  sound (`genResCertHead_sound`), and when it fails `degenPair_relation`
  (`Computable/HexpDegenerateComplete.lean`) builds integers `c ≠ 0`, `z`, `n_P` and the explicit
  solution `y = ∏_P P^(-n_P)` of `y′ + (c η₂ + z η₁) y = 0`. So, for simple-pole data over `ℚ`
  with rational residue polynomials, the head certificate holds exactly when `η₂` is independent
  of `η₁` modulo logarithmic derivatives. Its exactness relies on the completeness of Kronecker's
  factorisation (`Computable/KronComplete.lean`), which is also proved: `noFactor_complete`,
  `irredQ_complete`, `findFactor_complete` via Gauss's lemma and uniqueness of interpolation, and
  `factorQ_spec` (with enough fuel `factorQ` returns certified irreducible factors whose product is
  the input up to a non-zero constant). Over `ℚ` the unverified preprocessing is
  also proved always to succeed (`Computable/HexpDegenerateDecide.lean`: `lcmSq_spec`,
  `resPoly_spec`, `toRatL_ratQ`, `squarefreeCheck_complete'`). The end-to-end
  `hexpDegen_complete` then states: if `hexpDegen` fails, the simple-pole parts of `η₁` and `η₂`
  satisfy an explicit relation `y′ + (c r₂/s₂ + z r₁/s₁) y = 0` with `c ≠ 0` and `y ≠ 0`. So
  `hexpDegen` decides degenerate pairs over `ℚ` exactly. The whole certificate is also exact over
  `ℚ`: `hexpHexpIndepAll_iff` (`Computable/HexpHexpComplete.lean`) proves that `hexpHexpIndepAll`
  holds **iff** `y′ + (c η₂ + z η₁) y = 0` has only the zero solution for all integers `c ≠ 0`,
  `z`. That is, the precondition `hind` of `integrateHexpHexp_decides` is exactly the condition
  that `t₂` is a new hyperexponential over `ℚ(x)(t₁)`. Its completeness half,
  `hexpHexpIndepAll_complete`, covers the remaining failure of the Hermite-part branch: there
  `k η₁ᴴ + η₂ᴴ = 0` and every residue of the reduced `k η₁ + η₂` is rational. A residue-matching
  lemma (`residue_match`) and `ratResidue_logDeriv` then build `y`. The older identity-based `degenCertQ` is kept as a fast path.) An
  exponential with `t₁`-dependent argument over a
  general hyperexponential is decided by `Tower.integrateExpArgHexp`; its special-denominator bound
  (`Computable/HexpSpecialBound.lean`) is complete without any heuristic: if `z a₀′ - r η` is a
  logarithmic derivative then the Hermite part of `η` satisfies `r ηᴴ = z a₀′`
  (`deriv_eq_zero_of_add_proper_eq_logDeriv`, `RDE/LogDerivRigid.lean`), which determines `r`
  or, when `ηᴴ = 0`, is excluded by the monomial certificate. `x^α` with `α ∈ ℚ` is algebraic (not a monomial);
* **change of variables** (`Elementary/Rescale.lean`): `hasElementaryIntegral_rescale_iff` — `∫ f`
  is elementary for `∂` iff `∫ φ f` is for `φ∂` (`φ ≠ 0`; logarithms, exponentials and algebraic
  elements are preserved by rescaling the derivation);
* **genus zero** (`Algebraic/Genus0.lean`): `genus0_elementary` — in `Kc(x, y)`, `y² = ax² + bx + c`
  (`b² ≠ 4ac`, `√a ∈ Kc`), **every** element has an elementary integral (Euler's substitution
  `t = y − √a x` makes the field `Kc(t)`; rescaling by `1/t′` and rational integrability), e.g.
  `∫ dx/√(x²+1)` (`asinh_elementary`); `genus0_elementary_root` — the same when the quadratic has a
  root in `Kc` (`t = y/(x − e)`), e.g. `∫ dx/√(1−x²)` (`arcsin_elementary`), both via
  `hasElementaryIntegral_of_generated` (a function field generated over the constants by one
  non-constant element is elementary-integrable throughout); and in general
  `genus0_elementary_gen` — **every** element of `Kc(x, √(ax²+bx+c))` (`a ≠ 0`, `b² ≠ 4ac`) has an
  elementary integral, with no condition on `a` or the roots (`√a` is adjoined:
  `Elementary/SqrtExt.lean`), e.g. `∫ dx/√(3−2x²)`.
* **arbitrary elliptic models via change of variables**: `ellDecideCubic`
  (`Algebraic/EllCubic.lean`) for any squarefree cubic `y² = λx³ + μx² + νx + ρ` over `ℚ` (the
  substitution `X = λk²x`, `Z = λk³y` to an integral Weierstrass curve, with the derivation rescaled
  by `1/(λk²)`), and `ellDecideQuartic` (`Algebraic/EllQuartic.lean`) for quartics `y² = q(x)` with a
  rational root `e` (`t = 1/(x − e)`, `Y = y t²`, derivation rescaled by `−1/t²`); both with proved
  specs (`…_spec`: every answer correct) and kernel-checked examples: `∫ dx/√(4x³−4)` and
  `∫ dx/√(x⁴−1)` not elementary, `∫ x dx/√(x⁴−1)` elementary. The general front end
  `ellDecideAny` (`Algebraic/EllGenTw.lean`, used by both) also routes residues at points with
  irrational `y` (one class `d·ℚ²`) to `ellDecideTw` (`ellDecideGenTw_spec`), so e.g.
  `∫ dx/((x−2)√(x⁴−1))` (residue at `(2, √15)`) is decided;
* **mixed towers over a genus-zero base** (`Algebraic/Genus0Tower.lean`): after Euler's
  substitution and rescaling, a tower of logarithms/exponentials over `Kc(x, √(quadratic))` is a
  transcendental tower over `Kc(t)` with `t′ = 1`, decided by `nestX_decides`; e.g.
  `∫ log(x + √(x²+1))/x dx` (`∫ asinh(x)/x`) is **not elementary**
  (`asinh_div_x_not_elementary`). **Automated** (`Algebraic/Genus0Auto.lean`,
  `Genus0AutoSq.lean`): towers are given by *input codes* over `Kc(x, y)` (level `0`: `u(x) + v(x)y`);
  the translation `tr` substitutes a rational parametrisation `x = P(t)/Q(t)`, `y = R(t)/S(t)`
  (homogenised substitution, `evN_tr`: semantically exact), logarithmic levels become
  `.prim (ρ · tr η)` with `ρ = 1/t′`, exponential levels keep their argument; `genus0_decides`: with
  `certX` on the translated tower, `∫ A` is elementary iff `elemNX` answers `true` on `ρ · tr A`.
  `genus0_sq_decides` instantiates Euler's substitution `t = y − s x` for any
  `y² = s²x² + bx + c` (`b² ≠ 4s²c`; `euler_sq`). Examples (`Algebraic/Genus0AutoExample.lean`,
  all computed and kernel-checked): `∫ asinh(x)/x` not elementary, `∫ asinh x` elementary.
  `genus0_root_decides` (`Algebraic/Genus0AutoRoot.lean`, `euler_root`) covers every
  `y² = (x − e)(Ax + k)` (`Ae + k ≠ 0`) through `t = y/(x − e)`, whatever the leading coefficient;
  examples (`Algebraic/Genus0AutoRootExample.lean`): `∫ log x/√(2x²−2)` not elementary,
  `∫ x log x/√(2x²−2)` elementary. More generally `genus0_pt_decides`
  (`Algebraic/Genus0AutoPt.lean`, `euler_pt`): any conic `y² = q(x)` with a rational point
  `(x₀, y₀)` (`t = (y − y₀)/(x − x₀)`); e.g. (`Genus0AutoPtExample.lean`) `∫ log x/√(3x²+1)` not
  elementary, `∫ x log x/√(3x²+1)` elementary. (Conics without rational points, e.g. `y² = −x² − 1`, are handled instead as base curves of the
  mixed-tower decision, `Mixed/ConicExamples`.)
* the algebraic case (Trager, Bronstein) — **started, partial**:
  `Differential.hyp_decides` (`Algebraic/HypDecide.lean`) decides `∫ B(x) dx / √p(x)` for every
  polynomial `B ∈ ℚ[x]` and every squarefree `p ∈ ℚ[x]` of odd degree, in any differential field
  `E = Kc(x)(y)`, `y² = p(x)`, with constants `Kc`. The reduction `hypRed` (computable,
  `Algebraic/HypRed.lean`) writes `B = C′p + Cp′/2 + B₀`, `deg B₀ ≤ deg p − 2` (so
  `∫ B/y = C y + ∫ B₀/y`, `hyp_antiderivative`); `∫ B₀/y` is elementary iff `B₀ = 0`
  (`hyp_core`, `Algebraic/HypCore.lean`: from the `y`-component of a Liouville identity with
  `ℚ`-independent constants (`logSum_qindep`, `Algebraic/QIndep.lean`), the logarithmic terms have
  at most simple poles whose residues `∓mᵢ√p` must cancel, so every norm `aᵢ² − bᵢ²p` divides `p`,
  which by parity kills the logarithmic part; then `2B₀ = 2pe′ + p′e` has only `e = 0`). Kernel
  examples (`Algebraic/HypExample.lean`): `∫ dx/√(x³+1)`, `∫ x dx/√(x³+1)` not elementary,
  `∫ 3x²/(2√(x³+1)) dx = √(x³+1)`. **Finite poles** (`Algebraic/HypCert.lean`):
  `hyp_decides_cert` decides `∫ A(x)/(D(x)√p(x)) dx` whenever the Hermite reduction absorbs all
  finite poles, `A/(Dy) = (W/V·y)′ + B₀/y` (a polynomial identity checked by the kernel; found by
  the linear-algebra solver `hypCertSolve`): elementary iff `B₀ = 0`. `hypCertDecide` returns
  `some b` (proved correct, `hypCertDecide_spec`) or `none` when a genuine simple-pole
  (logarithmic) part remains. Examples: `∫ (x³−2)/(2x²√(x³+1)) = √(x³+1)/x`,
  `∫ (x³+2x²−2)/(2x²√(x³+1))` not elementary. **Completeness** (`Algebraic/HypCertComplete.lean`,
  `hypCertDecide_decides`, any odd degree, any genus): if `D` splits over `ℚ` and all its roots
  are branch points (roots of `p`), the Hermite decomposition has no logarithmic part, and
  `hypCertDecide` always answers; more generally (`hypCertDecide_decides_of_decomp`, any `D`) it
  answers whenever a residue-free Hermite decomposition `A/(Dy) = (W/D·y)′ + B₀/y` exists, i.e. it
  is complete on its whole domain. Genus-2 examples (`Algebraic/HypGenus2Example.lean`):
  `∫ dx/(x²√(x⁵−x))` not elementary, `∫ (3x⁴+1)/(2x√(x⁵−x)) dx = √(x⁵−x)/x`. **Logarithmic parts, elementary direction**
  (`Algebraic/HypLog.lean`): `hyp_log_cert` certifies `∫ A/(Dy) = (W/V)y + (1/K) log((a+by)/d)`
  from two kernel-checkable polynomial identities; example `∫ dx/(x√(x³+1)) = ⅓ log((y−1)²/x³)`.
  **Automatic certificate search, any genus** (`Algebraic/HypLogSearch.lean`). This applies when
  the poles are at rational non-branch points (so the residues `rᵢ` are rational). For
  `K = n·lcm(den rᵢ)`, `n = 1, 2, …`, `hypLogFind` looks for `u = (a + by)/d` with divisor
  `K Σ rᵢ([Pᵢ] − [P̄ᵢ])`. It lifts `y` to a square root `V` of `p` modulo `U = ∏(x−αᵢ)^{2|Krᵢ|}`
  (Lagrange, then Newton), solves `U ∣ a + bV` by a null space over the Riemann–Roch basis, and
  then solves linearly for the Hermite part `W`. Every candidate is re-checked against
  `hyp_log_cert` (`hypLogElem_sound`). `hypDecideLog` combines this with `hypCertDecide`
  (`hypDecideLog_spec`: every answer is correct). A `true` answer here proves elementarity. The
  opposite case — no `n` works, so the answer should be "not elementary" — needs a bound on
  torsion in the Jacobian; for genus ≥ 2 this is proved by hand-supplied certificates (see
  `Jacobian/`, "Not done") but not yet automated. Examples
  (`Algebraic/HypLogSearchExample.lean`, `decide +kernel`): `∫ dx/(x√(x⁵+1))` is elementary
  (genus 2: `(0,1)` has order 5 in the Jacobian, `u = (y − 1 − x⁵/2)/x⁵`), and so is
  `∫ dx/(x√(x³+1))`. **Galois orbits of poles** (`hypLogFindOrb`): for each irreducible factor
  `f` of `D` with a rational residue `z`, the poles are `(α, g(α))` with
  `g = A (z D′)⁻¹ mod f`. The square root `V` is lifted by CRT and Newton modulo `∏ f^{2|n|}`,
  and the rest of the search is unchanged, with the same `hyp_log_cert` check
  (`hypLogElemOrb_sound`). `hypDecideAllLog` combines everything (`hypDecideAllLog_spec`).
  Example: `∫ (3x⁵+4) dx/((x⁵−2)√(x⁵+x²−2))` is elementary (genus 2; the five poles over `x⁵ = 2`
  form the divisor of `(y − x)/(y + x)`).
  **Logarithmic parts on elliptic curves, non-elementary direction**
  (`Algebraic/EllDecide.lean`): `ell_torsion_of_elementary` — for `y² = x³ + ax² + bx + c`
  (`a, b, c ∈ ℤ`, squarefree), rational points `Pᵢ = (αᵢ, βᵢ)`, `βᵢ ≠ 0`, `zᵢ ∈ ℤ`, `D ≥ 1`: if
  `∫ (B(x) + Σ (zᵢ/D) βᵢ/(x − αᵢ)) / y dx` is elementary then `Σ zᵢ Pᵢ` has finite order in
  Mathlib's `E(ℚ)`. Ingredients built here: residues of the Liouville logarithms at `x = αᵢ`
  (`Algebraic/EllResidue.lean`, `EllGlue.lean`, `EllShape.lean`), the coordinate ring is a Dedekind
  domain (`Elliptic/Dedekind.lean`), Abel's theorem in the form "a norm `a² − b²p` whose zeros are
  the `(αᵢ, ±βᵢ)` gives `2 Σ mᵢ Pᵢ = 0`" via Mathlib's `toClass` (`Elliptic/Abel.lean`), transport
  `E(ℚ) → E(C)` (`Elliptic/Transport.lean`), and **Nagell–Lutz** (`Elliptic/NL*.lean`, new: torsion
  points are integral, `y² | disc`) with a kernel-checkable torsion test (`EllNL.torsionTest`,
  `torsionTest_spec`). Example (`Algebraic/EllExample.lean`): `∫ 5 dx / ((x−3)√(x³−2))` is not
  elementary, since `2·(3,5) = (129/100, −383/1000)` is non-integral.
  **Removing a logarithmic part** (`Algebraic/EllLog.lean`): `ell_log_reduce` — if
  `G = c·M/N + R` for `u = a + by` (`N = a² − b²p`, `M = 2p(ab′ − a′b) + abp′`, a polynomial
  identity) then `∫ G/y` is elementary iff `∫ R/y` is (since `u′/u = N′/(2N) + M/(2Ny)`).
  **The decision procedure** (`Algebraic/EllAlgo.lean`): `EllAlgo.ellDecide a b c B pts D fuel`
  for `(B(x) + Σ (zᵢ/D) βᵢ/(x − αᵢ)) / √(x³ + ax² + bx + c)` with rational points: the
  Nagell–Lutz torsion test on `S = Σ zᵢPᵢ`; if `S` has infinite order, *not elementary*; if `nS = 0`,
  an untrusted linear solve (`ellSolve`: Hensel-lifted local expansions of `y`, `nullBasis`) for
  `u = A + By` vanishing to order `n|zᵢ|` at `(αᵢ, sign(zᵢ)βᵢ)`, the kernel check of
  `G = (1/(nD)) M/N + R`, and `hypRed` on `R`. `ellDecide_spec`: every answer `some b` is correct
  (the whole procedure runs inside `decide +kernel`, ~3 s). Examples
  (`Algebraic/EllAlgoExample.lean`, `Algebraic/EllExample.lean`): `∫ (x³+1)/(x√(x³+1))` and
  `∫ (x+1)/((x−2)√(x³+1))` elementary; `∫ 3/((x−2)√(x³+1))`, `∫ (3/(x−2) − 1/x)/√(x³+1)`
  (torsion divisor, but an elliptic remainder) and `∫ (5/(x−3) + x)/√(x³−2)` (non-torsion) not
  elementary. **Completeness** (`Algebraic/EllComplete.lean`, `ellDecide_decides`): on valid input
  with `EllNL.fuelBound a b c` fuel, `ellDecide` returns `some b` and `b` is the truth — a proved
  decision procedure for this class. Ingredients: an explicit fuel bound for the torsion test
  (`Elliptic/NLFuel.lean`: undecided multiples are distinct integral points in a box; squarefree ⇒
  `disc ≠ 0`), the semantics of the solver (`Algebraic/EllSolve.lean`: Hensel lift, column
  blocks ⇔ local vanishing), existence of `u` over `ℚ` (`Algebraic/EllExist.lean`: `Point.toClass`
  injective ⇒ `∏ ⟨x−αᵢ, y−yᵢ⟩^{mᵢ}` principal; evaluation `x ↦ α + t`, `y ↦ Y(t)` into `ℚ[t]/(tᵐ)`;
  conjugation `y ↦ −y` bounds the norm, hence the degrees), `nullBasis` completeness, and "every
  non-zero solution is a valid certificate" (`Algebraic/EllCertValid.lean`: the norm is
  `λ ∏ (x−αᵢ)^{mᵢ}`, and `M ≡ mᵢ yᵢ (x−αᵢ)^{mᵢ−1} N₁` gives the residues). **General integrands**
  (`Algebraic/EllGen.lean`): `ellDecideGen a b c A D fuel` for `∫ A(x) / (D(x) √p(x)) dx` — an
  untrusted Hermite reduction (`V = D`) to `(W/D · y)′ + (B₀ + Σ c_α/(x − α))/y` over the rational
  roots of `D`, residues `c_α = (z/D′)√p(α)` with `√p(α) ∈ ℚ`, a kernel-checked identity, then
  `ellDecide`; `ellDecideGen_spec`: every answer is correct. **Completeness**
  (`Algebraic/EllGenComplete.lean`, `ellDecideGen_decides`): if `D` splits over `ℚ` and `p(α)` is
  a rational square at every root `α` of `D` off the branch points, `ellDecideGen` with
  `fuelBound` fuel always answers. The ingredients are the Hermite decomposition on `y² = p`
  (`Algebraic/HermiteExist.lean`: existence in any differential field with split `D`;
  `Algebraic/HermitePoly.lean`: its polynomial form over `ℚ(x)`; `Algebraic/HermiteBound.lean`:
  `deg W ≤ max(deg A, deg D)`, so it fits the solver's budget; `Algebraic/HermiteUnique.lean`:
  uniqueness via pole orders), a basis vector of the solver's null space with non-zero head, and
  the fact that any solver output passes the kernel check. `Algebraic/EllGenCompleteTw.lean`,
  `ellDecideAny_decides`: if the values `p(α)` all lie in one class `d₀·ℚ²`, the dispatcher
  `ellDecideAny` answers with the explicit fuel `fuelAny` (the maximum of the twists' bounds over
  the rational roots of `D`). The completeness carries over to arbitrary cubics
  (`Algebraic/EllCubicComplete.lean`, `ellDecideCubic_decides`: the normalization always succeeds
  and preserves the square class of `p(α)`) and to quartics with a rational root
  (`Algebraic/EllQuarticComplete.lean`, `ellDecideQuartic_decides`: reversal preserves
  squarefreeness and splitting, `sepCheck` is complete; the pole at `t = 0` — the points at
  infinity — requires the leading coefficient in the same class when `deg A ≥ 1`). Examples (`Algebraic/EllGenExample.lean`): `∫ (x³−6x²−2)/(2(x−2)²√(x³+1))` elementary,
  `∫ 1/((x−2)²√(x³+1))` not. **Residues at points with irrational `y`** (quadratic twists,
  `Elliptic/Scale.lean`, `Elliptic/Twist.lean`, `Algebraic/EllTwist.lean`,
  `Algebraic/EllAlgoTw.lean`): for points `(αᵢ, γᵢ√d)` (`dγᵢ² = p(αᵢ)`), over any constant field
  (`√d` is adjoined to the elementary extension when needed: `Elementary/SqrtExt.lean`,
  `exists_sqrt_ext`), `ell_torsion_twist` (elementary ⇒ `∑ zᵢ (dαᵢ, d²γᵢ)` torsion on
  the twist `Y² = X³ + adX² + bd²X + cd³`; transport `E^d(ℚ) → E(C)` by base change and the
  scaling isomorphism `(x, y) ↦ (u²x, u³y)`, proved additive), `ell_log_reduce_twist`
  (`u = A + √d B y`), and the decision procedure `ellDecideTw` with `ellDecideTw_spec` (every answer
  correct) and completeness (`Algebraic/EllCompleteTw.lean`, `ellDecideTw_decides`: with the twist's
  `fuelBound` it always answers; the existence of `u` is transported from the twist by `X = dx`,
  using uniqueness of Hensel lifts). Examples (`Algebraic/EllTwistExample.lean`):
  `∫ 2/(x√(x³+2))` elementary (twist point `(0, 4)` on `Y² = X³ + 16` has order 3),
  `∫ 1/((x−2)√(x³−1))` not (twist point `(14, 49)` on `Y² = X³ − 343`). **Residues in two quadratic classes**
  (`Algebraic/EllMixed.lean`, `Algebraic/EllAlgoMix.lean`): `ell_torsion_mixed` — if the integral
  with residues at points `(αᵢ, γᵢ√d₁)` and `(αᵢ, γᵢ√d₂)` (`d₁d₂` not a square) is elementary, the
  class-`d₂` divisor is torsion on the twist by `d₂` (a `ℚ`-linear functional on the constants with
  `λ(√d₂) = 1`, `λ(√d₁) = 0` turns the residue relations into integer weights for the
  per-logarithm Abel relations `ell_abel_log`); `ellDecideMix` certifies the class `d₂` by its
  torsion certificate, folds the polynomial remainder into `B` (`ell_log_reduce_twist'_add`) and
  decides the rest with `ellDecideTw`; `ellDecideMix_spec` (every answer correct) and
  `ellDecideMix_decides` (with the two twists' fuel bounds it always answers). Examples
  (`Algebraic/EllMixExample.lean`): `∫ (2 + 4/x − 12/(x+4))/√(x³+16)` elementary,
  `∫ (4/x − 12/(x+4))/√(x³+16)` and `∫ (3/(x−2) + 2/(x−1))/√(x³+1)` not. General integrands
  (`Algebraic/EllGenMix.lean`, `Algebraic/EllGenMixComplete.lean`): `residuePtsMix` splits the
  Hermite residues into the class of the first one and the rest; the dispatcher `ellDecideAll`
  (rational residues, one twist class, two classes) is correct (`ellDecideAll_spec`) and complete
  whenever the values `p(α)` at the roots of the split denominator lie in at most two quadratic
  classes (`ellDecideAll_decides`, fuel `fuelAny`); `ellDecideCubic`/`ellDecideQuartic` now use it
  (their decision theorems allow two classes). **Any number of classes — the elliptic case with
  split denominator is decided** (`Algebraic/EllMulti.lean`, `EllAlgoMulti.lean`, `EllGenMulti.lean`,
  `EllGenMultiComplete.lean`): square roots of distinct square classes are `ℚ`-linearly
  independent (`SqrtIndep.sqrt_indep`, `Elementary/SqrtIndep.lean`: the compositum of the
  quadratic fields is Galois over `ℚ` and its automorphisms separate the classes), so
  `ell_torsion_multi` makes every class's divisor torsion on its twist; `ellDecideMulti` folds the
  certificates of all classes but one into `B`; `groupCls` groups the Hermite residues by class.
  **`ellDecideEll_decides`**: for `y² = x³ + ax² + bx + c` squarefree and any `A, D ∈ ℚ[x]` with
  `D` split over `ℚ`, `ellDecideEll` (fuel `fuelAny`) answers, and its answer is the truth — no
  condition on the residues. `ellDecideCubic`/`ellDecideQuartic` use it, so their decision
  theorems (`ellDecideCubic_decides`, `ellDecideQuartic_decides`) need only a split denominator.
  Example (`Algebraic/EllMultiExample.lean`): `∫ dx/((x³+3x²−4x)√(x³+16))` (three classes) not
  elementary. **Non-split denominators, rational residues on Galois orbits**
  (`Algebraic/EllOrbit.lean`): take an irreducible factor `f` of `D` whose poles `(α, g(α))`
  (`f ∣ p − g²`) carry a rational residue `z`. Subtracting `z · d log((y − g)/(y + g))`
  (`orbit_logDeriv`: `= (p′g − 2g′p)/((p − g²) y)`) moves those residues to the roots of
  `(p − g²)/f`, which has lower degree. This is Cantor reduction in the Jacobian. `ellDecideOrbit`
  iterates it until the denominator splits, then calls `ellDecideEll`. The steps come from an
  untrusted search (Kronecker factors, modular inverses, a rational square root of
  `T²/(f′²p) mod f`), and each is checked by a polynomial identity (`stepOk`).
  `ellDecideOrbit_spec` proves that every answer is correct. **Completeness for quadratic
  and cubic orbits** (`Algebraic/EllOrbitComplete.lean`): for the class `OrbCls` — every
  non-linear irreducible factor of `D` is a simple quadratic or cubic, prime to `p` and `A`, with
  a rational residue
  (`f ∣ A² − z²D′²p`) — `ellDecideOrbitAuto_decides` proves that `ellDecideOrbitAuto` always
  answers, correctly. The proof goes through: `orbitStep_spec` (every Cantor step succeeds and
  passes its check; `h = (p − g²)/f` has degree ≤ 1); `orbCls_step` (the class is preserved,
  with one non-linear factor fewer);
  `factorQ_natDegree_le`; `orbitSearch_complete` (the reduction ends with a split denominator);
  then `ellDecideEll_decides`. Examples (`Algebraic/EllOrbitExample.lean`, `decide +kernel` in about 5 s):
  `∫ −2 dx/((x²+1)√(x³+x−1))` is not elementary (its residues move to the non-torsion point
  `(1,1)`), and `∫ (x³−x+2) dx/((x²+1)(x−1)√(x³+x−1))` is elementary. **Quartics with a square leading coefficient** (no rational root needed;
  `Algebraic/EllQuarticSq.lean`): the points at infinity are rational; the model change
  `X = y − s x² − (a/2s) x − β`, `W = (4s x + a/s) X − c′` gives `W² = P(X)` (cubic, proved
  generically: `W² − P(X) = 8sX (y² − q(x))`), `Kc(x, y) = Kc(X, W)` (via `hypField`), `X′ ≠ 0`
  (else `q` would be a square); after rescaling by `1/X′` the integrand is split as
  `R₁(X) + R₂(X) W` by an untrusted computation in `ℚ(X)[W]` checked by the kernel in
  `ℚ[x][y]/(y² − q)`; the rational part is elementary and `R₂ P / W` goes to `ellDecideCubic`.
  `ellDecideQuarticSq_spec`: every answer is correct (completeness not yet proved). Examples
  (`Algebraic/EllQuarticSqExample.lean`): `∫ dx/√(x⁴+1)` not elementary, `∫ x dx/√(x⁴+1)` and
  `∫ dx/(x√(x⁴+1))` elementary. **Quartics with any rational point** `(x₀, y₀)`, `y₀ ≠ 0`
  (`Algebraic/EllQuarticPt.lean`, `ellDecideQuarticPt_spec`): `t = 1/(x − x₀)`, `Y = y t²` give a
  quartic with square leading coefficient `y₀²`, then `ellDecideQuarticSq`; e.g.
  `∫ dx/√(2x⁴+1)` not elementary, `∫ x dx/√(2x⁴+1)` elementary. Not covered by these
  elliptic procedures (the general ones in the status table cover most of this list): residues at
  non-rational points or with non-rational residues (points over number fields, Mordell–Weil
  torsion over number fields), genus ≥ 2 (Jacobian torsion); even-degree `p`
  (logarithmic parts on the curve: deciding them requires the torsion test for divisors in the
  Jacobian — Riemann–Roch spaces and torsion bounds, absent from Mathlib), general algebraic
  function fields (integral bases, Trager's Hermite reduction), and mixed algebraic–transcendental
  towers (Bronstein);
* antiderivatives: proved identities `Tower.integratePrimData_antiderivative`,
  `Tower.integrateExp_antiderivative`, `Tower.integrateHyperexp_antiderivative`,
  `Tower.integrateHyperexpW_antiderivative`,
  `CPoly.prim2Loop_antiderivative`, `Tower.integratePrim2_antiderivative`,
  `Tower.integrateNestedLog_antiderivative`, `Tower.integrateExpPrim_antiderivative`,
  `Tower.integrateExpExp_antiderivative`, `Tower.integratePrimExp_antiderivative` (height three:
  `A / D = (gn / gd + W)′ + ρ + rem / s`) give the closed-form part explicitly; the logarithmic part is
  left as a sum over the roots of `s` (not expanded into a term language).

The only ingredient that may ever be assumed rather than proved is the correctness of a
zero-equivalence oracle for constants (`Computable/ZeroOracle.lean`); nothing currently uses it.

## Building

```
lake build
```

Some example files check large certificates in the kernel (`decide +kernel`) and need about
10 GB each (`Torsion/TriExample.lean`, `Torsion/TriAutoExample.lean`, …). On machines with less
than ~40 GB of memory, build them one at a time before the full build, e.g.
`lake build RischTragerBronstein.Torsion.TriExample`, then
`lake build RischTragerBronstein.Torsion.TriAutoExample`, then `lake build`.
