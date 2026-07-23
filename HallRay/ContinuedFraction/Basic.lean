import HallRay.Basic

/-!
# Continued fractions

Basic continued-fraction API needed throughout the project.

Planned contents:

* finite continued fractions attached to words of positive integers;
* values of infinite continued fractions;
* convergents and their denominator growth;
* convergence for a common prefix and bounds on cylinder diameters.
-/

namespace HallRay
namespace ContinuedFraction

/-- A positive integer, used as a partial quotient. -/
abbrev PartialQuotient := {n : ℕ // 0 < n}

/-- A finite word of positive partial quotients. -/
abbrev Word := List PartialQuotient

/--
Evaluate the fractional tail

`1 / (a₁ + 1 / (a₂ + ... + 1 / aₙ))`.
-/
noncomputable def finiteTail (digits : Word) : ℝ :=
  digits.foldr (fun a x ↦ 1 / ((a.1 : ℝ) + x)) 0

/-- The finite continued fraction `[head; digits]`. -/
noncomputable def finiteValue (head : ℝ) (digits : Word) : ℝ :=
  head + finiteTail digits

/-- The convergent obtained from the first `n` partial quotients of `digits`. -/
noncomputable def convergent (head : ℝ) (digits : ℕ → PartialQuotient) (n : ℕ) : ℝ :=
  finiteValue head ((List.range n).map digits)

/--
The value `[head; digits 0, digits 1, ...]` of an infinite continued fraction.

Convergence for positive partial quotients will be proved separately.  Using
`Filter.limUnder` gives a total definition while agreeing with the usual
limit whenever the convergents tend to one.
-/
noncomputable def value (head : ℝ) (digits : ℕ → PartialQuotient) : ℝ :=
  Filter.limUnder Filter.atTop (convergent head digits)

end ContinuedFraction
end HallRay
