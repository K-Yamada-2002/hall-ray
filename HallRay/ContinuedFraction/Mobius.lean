import HallRay.ContinuedFraction.Basic

/-!
# Continued fractions as Möbius transformations

Algebraic facts about adjoining a finite common prefix to a continued
fraction.

Planned contents:

* the map `Φ_w`;
* its expression using consecutive convergents;
* the determinant identity;
* the common-prefix length formula;
* the exact inequalities used in Hall's length condition.
-/

namespace HallRay
namespace ContinuedFraction

/--
Adjoin the finite word `w` before the complete quotient `x`:

`prefixMap w x = [0; w₁, ..., wₙ, x]`.
-/
noncomputable def prefixMap (w : Word) (x : ℝ) : ℝ :=
  w.foldr (fun a y ↦ 1 / ((a.1 : ℝ) + y)) (1 / x)

end ContinuedFraction
end HallRay
