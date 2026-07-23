import HallRay.Basic

/-!
# Intervals and Minkowski sums

General real-set lemmas used in Hall's argument.

Planned contents:

* Minkowski addition of subsets of `ℝ`;
* the two-closed-interval lemma;
* invariance of a finite union's self-sum after removing one short gap;
* Minkowski sums and intersections of decreasing nonempty compact sets.
-/

namespace HallRay
namespace Interval

/-- The Minkowski sum `X + Y = {x + y | x ∈ X, y ∈ Y}`. -/
def minkowskiSum (X Y : Set ℝ) : Set ℝ :=
  Set.image2 (· + ·) X Y

end Interval
end HallRay
