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
open ContinuedFraction

/-- Arithmetic decomposition used at the start of the Hall-ray argument. -/
theorem exists_large_partialQuotient (ell : ℝ) (hell : 6 ≤ ell) :
    ∃ a : PartialQuotient,
      5 ≤ a.1 ∧
      ell - a.1 ∈
        Set.Icc (Real.sqrt 2 - 1) (4 * Real.sqrt 2 - 4) := by
  let t : ℝ := ell - (Real.sqrt 2 - 1)
  have hspos : (0 : ℝ) < Real.sqrt 2 := Cantor.sqrt_two_pos
  have hslt : Real.sqrt 2 < (2 : ℝ) := Cantor.sqrt_two_lt_two
  have ht5 : (5 : ℝ) ≤ t := by
    dsimp [t]
    linarith
  have ht0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht5
  let n : ℕ := ⌊t⌋₊
  have hn5 : 5 ≤ n := by
    apply (Nat.le_floor_iff ht0).2
    simpa [n] using ht5
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn5
  let a : PartialQuotient := ⟨n, hnpos⟩
  refine ⟨a, hn5, ?_⟩
  have hfloor : (n : ℝ) ≤ t := by
    simpa [n] using Nat.floor_le ht0
  have hsucc : t < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one t
  have hs43 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Cantor.sqrt_two_sq]
  change Real.sqrt 2 - 1 ≤ ell - (n : ℝ) ∧
    ell - (n : ℝ) ≤ 4 * Real.sqrt 2 - 4
  constructor
  · dsimp [t] at hfloor
    linarith
  · dsimp [t] at hsucc
    linarith

/-- Hall's ray obtained by Hall's continued-fraction construction. -/
theorem hall_ray : Set.Ici (6 : ℝ) ⊆ spectrum := by
  intro ell hell
  obtain ⟨a, ha, hrem⟩ := exists_large_partialQuotient ell hell
  have hsum :
      ell - (a.1 : ℝ) ∈
        Interval.minkowskiSum (Cantor.C 4) (Cantor.C 4) := by
    rw [Cantor.hall_C4]
    exact hrem
  rcases hsum with ⟨x, hx, y, hy, hxy⟩
  rcases hx with ⟨b, hb, rfl⟩
  rcases hy with ⟨c, hc, rfl⟩
  have htarget :
      (a.1 : ℝ) + ContinuedFraction.value 0 c +
          ContinuedFraction.value 0 b = ell := by
    linarith
  rw [← htarget]
  apply large_value_mem_spectrum a b c ha hb hc
  rw [htarget]
  exact hell

end HallRay
