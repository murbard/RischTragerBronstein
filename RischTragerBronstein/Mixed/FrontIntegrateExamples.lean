import RischTragerBronstein.Mixed.FrontIntegrate

/-!
# Examples: antiderivatives from the front end

`integrateShow` runs `frontIntegrate` (`elMW` behind `frontDecide`) and prints the tower and the
pieces of the antiderivative; `frontIntegrate_valid` proves that every printed antiderivative is
valid. Over the line `y = x` (base `ℚ(x)`):

* `∫ x exp(x²) = ½ t₀`, `t₀ = exp(x²)`;
* `∫ dx/(x log x) = ∑_{x a = 0} log (t₀ − a) = log (log x)`;
* `∫ (log x + 1) = x t₀`;
* `∫ exp(eˣ) eˣ = t₁`;
* `∫ 2 log x/(x (log² x − 2)) = ∑_{x a² − 2x = 0} log (t₀ − a) = log (log² x − 2)`;
* `∫ exp(x²)` is not elementary;
* `∫ dx/(x² + 1) = ∑_{a² + 1 = 0} log(x − a)/(2a)` (`= arctan x`): on a line the base part is
  integrated explicitly (`baseRat`, `baseRat_spec`, `ratLog_explicit` in `Mixed/MTBaseLine`);
* on the conic `y² = −x² − 1` (`#eval`, about 4 min, not in the build):
  `∫ x log x/y = −y t₀ + y + g log((y − g)/x)` with `g² = −1` — the base part from the curve
  witness of the total decision (`baseCurveW`, `baseCurve_explicit`).
-/

namespace Curves.MT.FrontIntEx

open Curves.MT.Front EE

/-- The line `y − x = 0`. -/
def Fl : Sup.BPoly ℚ := [[0, -1], [1]]

#guard integrateShow Fl (mul x (exp (pow x 2))) 3 =
  ["elementary; tower:", "t0 := exp(1*x*x)", "antiderivative = sum of the pieces:",
    "level t0: ((((1/2)))*t0)", "base (rational in x): 0"]

#guard integrateShow Fl (inv (mul x (log x))) 3 =
  ["elementary; tower:", "t0 := log(x)", "antiderivative = sum of the pieces:",
    "level t0: sum over the roots a of ((1*x))*t0 (as a polynomial in t0) of (((1)))[t0 := a] * log(t0 - a)",
    "base (rational in x): 0"]

#guard integrateShow Fl (add (log x) (cst 1)) 3 =
  ["elementary; tower:", "t0 := log(x)", "antiderivative = sum of the pieces:",
    "level t0: (((1*x))*t0)", "base (rational in x): 0"]

#guard integrateShow Fl (mul (exp (exp x)) (exp x)) 3 =
  ["elementary; tower:", "t0 := exp(x)", "t1 := exp(exp(x))", "antiderivative = sum of the pieces:",
    "level t1: ((((1)))*t1)", "level t0: 0", "base (rational in x): 0"]

#guard integrateShow Fl (div (mul (cst 2) (log x)) (mul x (sub (pow (log x) 2) (cst 2)))) 3 =
  ["elementary; tower:", "t0 := log(x)", "antiderivative = sum of the pieces:",
    "level t0: sum over the roots a of ((-2*x)) + ((1*x))*t0^2 (as a polynomial in t0) of (((1)))[t0 := a] * log(t0 - a)",
    "base (rational in x): 0"]

#guard integrateShow Fl (exp (pow x 2)) 3 = ["not elementary"]

-- `∫ dx/(x² + 1) = ∑_{a² + 1 = 0} log(x − a)/(2a) = arctan x`: the base part on the line is
-- integrated by `integrateRational` (`baseRat_spec`, `ratLog_explicit`).
#guard integrateShow Fl (inv (add (pow x 2) (cst 1))) 3 =
  ["elementary; tower:", "antiderivative = sum of the pieces:",
    "base (rational in x): sum over the roots a of 1 + 1*x^2 of (1)/(2*a) * log(x - a)"]

end Curves.MT.FrontIntEx
