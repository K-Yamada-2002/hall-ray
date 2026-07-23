import HallRay.Lagrange.Basic

-- This project is MIT-licensed, while Mathlib's standard header linter only
-- accepts its Apache-2.0 header template.
set_option linter.style.header false

/-!
# Block sequences realizing large Lagrange values

The explicit two-sided sequence used to derive Hall's ray from Hall's theorem.

Planned contents:

* the finite blocks `B_n`;
* their concatenation with the distinguished partial quotient `a`;
* the positions `j_n`;
* convergence of `λ_(j_n)` to `a + x + y`;
* the strict upper bound away from the distinguished positions.
-/

namespace HallRay
namespace Lagrange

-- The block construction from §5 of `doc/main.tex` will be introduced here.

end Lagrange
end HallRay
