import HallRay.Cantor.Hall
import HallRay.Lagrange.BlockSequence

-- This project is MIT-licensed, while Mathlib's standard header linter only
-- accepts its Apache-2.0 header template.
set_option linter.style.header false

/-!
# Hall's ray

Final assembly of Hall's theorem and the explicit block sequence.

The target theorem is `[6, ∞) ⊆ L`.
-/

namespace HallRay

open Lagrange

/-- Hall's ray obtained by Hall's continued-fraction construction. -/
theorem hall_ray : Set.Ici (6 : ℝ) ⊆ spectrum := by
  sorry

end HallRay
