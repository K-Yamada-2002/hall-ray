import HallRay.ContinuedFraction.Basic

/-!
# The Lagrange spectrum

The two-sided continued-fraction presentation of the Lagrange spectrum.

Planned contents:

* positive-integer sequences indexed by `ℤ`;
* the local value `λ_i`;
* the Lagrange value defined by a limsup;
* the Lagrange spectrum `L`.
-/

namespace HallRay
namespace Lagrange

open ContinuedFraction

/-- A two-sided sequence of positive partial quotients. -/
abbrev BiSequence := ℤ → PartialQuotient

/-- Partial quotients to the right of position `i`. -/
def rightDigits (A : BiSequence) (i : ℤ) (n : ℕ) : PartialQuotient :=
  A (i + (n + 1 : ℕ))

/-- Partial quotients to the left of position `i`, read in reverse order. -/
def leftDigits (A : BiSequence) (i : ℤ) (n : ℕ) : PartialQuotient :=
  A (i - (n + 1 : ℕ))

/--
The local Lagrange value

`λᵢ(A) = [aᵢ; aᵢ₊₁, ...] + [0; aᵢ₋₁, ...]`.
-/
noncomputable def lambda (A : BiSequence) (i : ℤ) : ℝ :=
  value (A i).1 (rightDigits A i) + value 0 (leftDigits A i)

/-- The Lagrange value `limsup_{i → ∞} λᵢ(A)`. -/
noncomputable def lagrangeValue (A : BiSequence) : ℝ :=
  Filter.limsup (fun n : ℕ ↦ lambda A n) Filter.atTop

/--
The Lagrange spectrum in its two-sided continued-fraction presentation.

The boundedness condition expresses the finiteness requirement on the
limsup in Definition 1 of `doc/main.tex`.
-/
def spectrum : Set ℝ :=
  {ell | ∃ A : BiSequence,
    Filter.IsBoundedUnder LE.le Filter.atTop (fun n : ℕ ↦ lambda A n) ∧
      ell = lagrangeValue A}

end Lagrange
end HallRay
