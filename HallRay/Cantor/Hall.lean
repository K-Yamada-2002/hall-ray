import HallRay.Cantor.Construction
import HallRay.Interval.Minkowski

-- This project is MIT-licensed, while Mathlib's standard header linter only
-- accepts its Apache-2.0 header template.
set_option linter.style.header false

/-!
# Hall's theorem for `C(4)`

Assembly of the Cantor-set construction and the general Minkowski-sum lemmas.

The target theorem is

`C(4) + C(4) = [√2 - 1, 4 * √2 - 4]`.
-/

namespace HallRay
namespace Cantor

open Interval

/-- Hall's theorem: the self-sum of `C(4)` is an interval. -/
theorem hall_C4 :
    minkowskiSum (C 4) (C 4) =
      Set.Icc (Real.sqrt 2 - 1) (4 * Real.sqrt 2 - 4) := by
  sorry

end Cantor
end HallRay
