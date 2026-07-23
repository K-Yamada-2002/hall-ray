import HallRay.ContinuedFraction.Mobius

/-!
# Hall's continued-fraction Cantor set

The recursive interval construction of `C(4)`.

Planned contents:

* the periodic complete quotients `ξ` and `η`;
* the interval states `T₁`, `T₂`, and `T₃`;
* the gaps `G₁`, `G₂`, and `G₃` and their child rules;
* Hall's length condition;
* identification of the surviving set with `C(4)`;
* a nonincreasing enumeration of the gaps and the component lower bound.
-/

namespace HallRay
namespace Cantor

open ContinuedFraction

private def q1 : PartialQuotient := ⟨1, by omega⟩
private def q2 : PartialQuotient := ⟨2, by omega⟩
private def q3 : PartialQuotient := ⟨3, by omega⟩
private def q4 : PartialQuotient := ⟨4, by omega⟩

/--
The continued-fraction Cantor set

`C(N) = { [0; a₁, a₂, ...] | 1 ≤ aᵢ ≤ N }`.

The definition is meaningful for positive `N`; using `ℕ` as the parameter
keeps expressions such as `C 4` lightweight.
-/
def C (N : ℕ) : Set ℝ :=
  {x | ∃ digits : ℕ → PartialQuotient,
    (∀ n, (digits n).1 ≤ N) ∧ x = value 0 digits}

/-- The periodic complete quotient `[overline{4,1}]`. -/
noncomputable def xi : ℝ :=
  2 + 2 * Real.sqrt 2

/-- The periodic complete quotient `[overline{1,4}]`. -/
noncomputable def eta : ℝ :=
  (1 + Real.sqrt 2) / 2

/-- The interval `T₁(w)` from §2.2 of `doc/main.tex`. -/
noncomputable def T1 (w : Word) : Set ℝ :=
  Set.uIcc (prefixMap w eta) (prefixMap w xi)

/-- The interval `T₂(w)` from §2.2 of `doc/main.tex`. -/
noncomputable def T2 (w : Word) : Set ℝ :=
  Set.uIcc (prefixMap w xi) (prefixMap (w ++ [q2]) xi)

/-- The interval `T₃(w)` from §2.2 of `doc/main.tex`. -/
noncomputable def T3 (w : Word) : Set ℝ :=
  Set.uIcc (prefixMap w xi) (prefixMap (w ++ [q3]) xi)

/-- The open gap `G₁(w)` removed from `T₁(w)`. -/
noncomputable def G1 (w : Word) : Set ℝ :=
  Set.uIoo (prefixMap (w ++ [q1]) eta) (prefixMap (w ++ [q2]) xi)

/-- The open gap `G₂(w)` removed from `T₂(w)`. -/
noncomputable def G2 (w : Word) : Set ℝ :=
  Set.uIoo (prefixMap (w ++ [q2]) eta) (prefixMap (w ++ [q3]) xi)

/-- The open gap `G₃(w)` removed from `T₃(w)`. -/
noncomputable def G3 (w : Word) : Set ℝ :=
  Set.uIoo (prefixMap (w ++ [q3]) eta) (prefixMap (w ++ [q4]) xi)

end Cantor
end HallRay
