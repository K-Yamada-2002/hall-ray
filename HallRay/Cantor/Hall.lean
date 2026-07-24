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
open ContinuedFraction

theorem HallNode.minkowskiSum_interval_children (v : HallNode) :
    minkowskiSum v.interval v.interval =
      minkowskiSum (v.leftChild.interval ∪ v.rightChild.interval)
        (v.leftChild.interval ∪ v.rightChild.interval) := by
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      have horder := prefixMap_four_order w 1 (by omega) (by omega)
      have hlength := hall_length_condition w 1 (by omega) (by omega)
      have hsum := minkowskiSum_uIcc_split_self horder hlength.1 hlength.2
      simp only [HallNode.interval, HallNode.leftChild, HallNode.rightChild,
        T1, T2] at hsum ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      rw [eta_eq_one_add_delta, xi_eq_four_add_epsilon]
      simp only [q1_val, q2_val] at hsum ⊢
      norm_num at hsum ⊢
      simpa [Set.uIcc_comm, add_assoc, add_comm, add_left_comm] using hsum
  | two =>
      have horder := prefixMap_four_order w 2 (by omega) (by omega)
      have hlength := hall_length_condition w 2 (by omega) (by omega)
      have hsum := minkowskiSum_uIcc_split_self horder hlength.1 hlength.2
      simp only [HallNode.interval, HallNode.leftChild, HallNode.rightChild,
        T1, T2, T3] at hsum ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      rw [xi_eq_four_add_epsilon]
      simp only [q2_val, q3_val] at hsum ⊢
      norm_num at hsum ⊢
      simpa [Set.uIcc_comm, add_assoc, add_comm, add_left_comm] using hsum
  | three =>
      have horder := prefixMap_four_order w 3 (by omega) (by omega)
      have hlength := hall_length_condition w 3 (by omega) (by omega)
      have hsum := minkowskiSum_uIcc_split_self horder hlength.1 hlength.2
      simp only [HallNode.interval, HallNode.leftChild, HallNode.rightChild,
        T1, T3] at hsum ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      rw [xi_eq_four_add_epsilon]
      simp only [q3_val, q4_val] at hsum ⊢
      norm_num at hsum ⊢
      simpa [Set.uIcc_comm, add_assoc, add_comm, add_left_comm] using hsum

noncomputable def HallNode.intervalLength (v : HallNode) : ℝ :=
  match v.state with
  | .one => |prefixMap v.word xi - prefixMap v.word eta|
  | .two => |prefixMap (v.word ++ [q2]) xi - prefixMap v.word xi|
  | .three => |prefixMap (v.word ++ [q3]) xi - prefixMap v.word xi|

noncomputable def HallNode.gapLength (v : HallNode) : ℝ :=
  match v.state with
  | .one =>
      |prefixMap (v.word ++ [q2]) xi - prefixMap (v.word ++ [q1]) eta|
  | .two =>
      |prefixMap (v.word ++ [q3]) xi - prefixMap (v.word ++ [q2]) eta|
  | .three =>
      |prefixMap (v.word ++ [q4]) xi - prefixMap (v.word ++ [q3]) eta|

theorem HallNode.children_length_ge_gap (v : HallNode) :
    v.gapLength ≤ v.leftChild.intervalLength ∧
      v.gapLength ≤ v.rightChild.intervalLength := by
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      have h := hall_length_condition w 1 (by omega) (by omega)
      simp only [HallNode.gapLength, HallNode.intervalLength,
        HallNode.leftChild, HallNode.rightChild] at h ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      rw [xi_eq_four_add_epsilon]
      simp only [q1_val, q2_val] at h ⊢
      norm_num at h ⊢
      simpa [abs_sub_comm, add_assoc, add_comm, add_left_comm] using h
  | two =>
      have h := hall_length_condition w 2 (by omega) (by omega)
      simp only [HallNode.gapLength, HallNode.intervalLength,
        HallNode.leftChild, HallNode.rightChild] at h ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      rw [xi_eq_four_add_epsilon]
      simp only [q2_val, q3_val] at h ⊢
      norm_num at h ⊢
      simpa [abs_sub_comm, add_assoc, add_comm, add_left_comm] using h
  | three =>
      have h := hall_length_condition w 3 (by omega) (by omega)
      simp only [HallNode.gapLength, HallNode.intervalLength,
        HallNode.leftChild, HallNode.rightChild] at h ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      simp only [q3_val, q4_val] at h ⊢
      norm_num at h ⊢
      simpa [abs_sub_comm, add_assoc, add_comm, add_left_comm] using h

noncomputable def gapAt (w : Word) (k : ℕ) : ℝ :=
  |prefixMap w ((k : ℝ) + 1 + delta) -
    prefixMap w ((k : ℝ) + epsilon)|

theorem HallNode.gapLength_eq_gapAt (v : HallNode) :
    v.gapLength =
      gapAt v.word
        (match v.state with | .one => 1 | .two => 2 | .three => 3) := by
  rcases v with ⟨w, state⟩
  cases state <;>
    simp only [HallNode.gapLength, gapAt] <;>
    simp_rw [prefixMap_append_eta, prefixMap_append_xi] <;>
    simp only [q1_val, q2_val, q3_val, q4_val] <;>
    norm_num

theorem gapAt_succ_le (w : Word) (k : ℕ) (hk1 : 1 ≤ k) (_hk2 : k ≤ 2) :
    gapAt w (k + 1) ≤ gapAt w k := by
  let Cq : ℝ := (mobiusCoeffs w).C
  let Dq : ℝ := (mobiusCoeffs w).D
  let x1 : ℝ := (k : ℝ) + epsilon
  let x2 : ℝ := (k : ℝ) + 1 + delta
  let y1 : ℝ := (k : ℝ) + 1 + epsilon
  let y2 : ℝ := (k : ℝ) + 2 + delta
  have hC : 0 < Cq := by
    dsimp [Cq]
    exact_mod_cast mobius_C_pos w
  have hD : 0 ≤ Dq := by positivity
  have hx1 : 0 < x1 := by
    dsimp [x1]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith [epsilon_pos]
  have hx2 : 0 < x2 := by
    dsimp [x2]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith [delta_pos]
  have hy1 : 0 < y1 := by dsimp [y1]; linarith [hx1]
  have hy2 : 0 < y2 := by dsimp [y2]; linarith [hx2]
  have hnum : y2 - y1 = x2 - x1 := by
    dsimp [x1, x2, y1, y2]
    ring
  have h12 : x1 ≤ x2 := by
    dsimp [x1, x2, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have hy12 : y1 ≤ y2 := by linarith [hnum, h12]
  have hdx1 : 0 < Cq * x1 + Dq := by positivity
  have hdx2 : 0 < Cq * x2 + Dq := by positivity
  have hdy1 : 0 < Cq * y1 + Dq := by positivity
  have hdy2 : 0 < Cq * y2 + Dq := by positivity
  unfold gapAt
  push_cast
  have ey2 : (k : ℝ) + 1 + 1 + delta = y2 := by
    dsimp [y2]
    ring
  have ey1 : (k : ℝ) + 1 + epsilon = y1 := rfl
  have ex2 : (k : ℝ) + 1 + delta = x2 := rfl
  have ex1 : (k : ℝ) + epsilon = x1 := rfl
  rw [ey2, ey1, ex2, ex1]
  rw [abs_prefixMap_sub_prefixMap w hy2 hy1,
    abs_prefixMap_sub_prefixMap w hx2 hx1]
  change
    |y2 - y1| / ((Cq * y2 + Dq) * (Cq * y1 + Dq)) ≤
      |x2 - x1| / ((Cq * x2 + Dq) * (Cq * x1 + Dq))
  rw [abs_of_nonneg (sub_nonneg.2 hy12),
    abs_of_nonneg (sub_nonneg.2 h12), hnum]
  apply (div_le_div_iff₀ (mul_pos hdy2 hdy1) (mul_pos hdx2 hdx1)).2
  have hxy1 : Cq * x1 + Dq ≤ Cq * y1 + Dq := by
    gcongr
    dsimp [x1, y1]
    linarith
  have hxy2 : Cq * x2 + Dq ≤ Cq * y2 + Dq := by
    gcongr
    dsimp [x2, y2]
    linarith
  nlinarith [mul_le_mul hxy2 hxy1 hdx1.le hdy2.le]

noncomputable def alpha : ℝ := (6 - 2 * Real.sqrt 2) / 7
noncomputable def beta : ℝ := (2 * Real.sqrt 2 + 1) / 7

theorem alpha_eq_one_div_two_add_delta :
    alpha = 1 / (2 + delta) := by
  have hden : (2 : ℝ) + delta ≠ 0 := by linarith [delta_pos]
  apply (eq_div_iff hden).2
  unfold alpha delta
  nlinarith [sqrt_two_sq]

theorem beta_eq_one_div_one_add_epsilon :
    beta = 1 / (1 + epsilon) := by
  have hden : (1 : ℝ) + epsilon ≠ 0 := by linarith [epsilon_pos]
  apply (eq_div_iff hden).2
  unfold beta epsilon
  nlinarith [sqrt_two_sq]

theorem sqrt_two_cube : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
  rw [pow_succ, sqrt_two_sq]

theorem alpha_pos : 0 < alpha := by
  rw [alpha_eq_one_div_two_add_delta]
  exact one_div_pos.mpr (by linarith [delta_pos])

theorem alpha_lt_beta : alpha < beta := by
  unfold alpha beta
  nlinarith [sqrt_two_sq, sqrt_two_pos]

theorem appended_gap_one_le_gapAt (w : Word) (q k : ℕ)
    (hq1 : 1 ≤ q) (hq4 : q ≤ 4) (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (hrel : q = k ∨ (q = 4 ∧ k = 3)) :
    |prefixMap w ((q : ℝ) + beta) -
        prefixMap w ((q : ℝ) + alpha)| ≤ gapAt w k := by
  let Cq : ℝ := (mobiusCoeffs w).C
  let Dq : ℝ := (mobiusCoeffs w).D
  let c1 : ℝ := (q : ℝ) + alpha
  let c2 : ℝ := (q : ℝ) + beta
  let p1 : ℝ := (k : ℝ) + epsilon
  let p2 : ℝ := (k : ℝ) + 1 + delta
  have hC : 0 < Cq := by
    dsimp [Cq]
    exact_mod_cast mobius_C_pos w
  have hD : 0 ≤ Dq := by positivity
  have hDC : Dq ≤ Cq := by
    dsimp [Cq, Dq]
    exact_mod_cast mobius_D_le_C w
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hc1 : 0 < c1 := by dsimp [c1]; linarith [alpha_pos]
  have hc2 : 0 < c2 := by dsimp [c2]; linarith [alpha_lt_beta, alpha_pos]
  have hp1 : 0 < p1 := by dsimp [p1]; linarith [epsilon_pos]
  have hp2 : 0 < p2 := by dsimp [p2]; linarith [delta_pos]
  have hc12 : c1 ≤ c2 := by dsimp [c1, c2]; linarith [alpha_lt_beta]
  have hp12 : p1 ≤ p2 := by
    dsimp [p1, p2, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have hdc1 : 0 < Cq * c1 + Dq := by positivity
  have hdc2 : 0 < Cq * c2 + Dq := by positivity
  have hdp1 : 0 < Cq * p1 + Dq := by positivity
  have hdp2 : 0 < Cq * p2 + Dq := by positivity
  unfold gapAt
  rw [abs_prefixMap_sub_prefixMap w hc2 hc1,
    abs_prefixMap_sub_prefixMap w hp2 hp1]
  change
    |c2 - c1| / ((Cq * c2 + Dq) * (Cq * c1 + Dq)) ≤
      |p2 - p1| / ((Cq * p2 + Dq) * (Cq * p1 + Dq))
  rw [abs_of_nonneg (sub_nonneg.2 hc12),
    abs_of_nonneg (sub_nonneg.2 hp12)]
  apply (div_le_div_iff₀ (mul_pos hdc2 hdc1) (mul_pos hdp2 hdp1)).2
  dsimp [c1, c2, p1, p2, alpha, beta, delta, epsilon] at *
  rcases hrel with rfl | ⟨rfl, rfl⟩
  · interval_cases q <;> norm_num at * <;> ring_nf at * <;>
      simp only [sqrt_two_sq, sqrt_two_cube] at * <;>
      nlinarith [sqrt_two_sq, sqrt_two_pos,
        one_lt_sqrt_two, sqrt_two_lt_two,
        sq_nonneg Cq, sq_nonneg Dq, sq_nonneg (Cq - Dq),
        mul_nonneg hC.le hD, mul_nonneg hD (sub_nonneg.2 hDC)]
  · norm_num at *
    ring_nf at *
    simp only [sqrt_two_sq, sqrt_two_cube] at *
    nlinarith [sqrt_two_sq, sqrt_two_pos,
      one_lt_sqrt_two, sqrt_two_lt_two,
      sq_nonneg Cq, sq_nonneg Dq, sq_nonneg (Cq - Dq),
      mul_nonneg hC.le hD, mul_nonneg hD (sub_nonneg.2 hDC)]

theorem gapAt_append_one_eq (w : Word) (q : PartialQuotient) :
    gapAt (w ++ [q]) 1 =
      |prefixMap w ((q.1 : ℝ) + alpha) -
        prefixMap w ((q.1 : ℝ) + beta)| := by
  unfold gapAt
  rw [prefixMap_append_singleton, prefixMap_append_singleton]
  norm_num
  have ha : ((2 : ℝ) + delta)⁻¹ = alpha := by
    simpa only [one_div] using alpha_eq_one_div_two_add_delta.symm
  have hb : ((1 : ℝ) + epsilon)⁻¹ = beta := by
    simpa only [one_div] using beta_eq_one_div_one_add_epsilon.symm
  rw [ha, hb]

theorem gapAt_append_one_le (w : Word) (q : PartialQuotient) (k : ℕ)
    (hq4 : q.1 ≤ 4) (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (hrel : q.1 = k ∨ (q.1 = 4 ∧ k = 3)) :
    gapAt (w ++ [q]) 1 ≤ gapAt w k := by
  rw [gapAt_append_one_eq]
  simpa [abs_sub_comm] using
    appended_gap_one_le_gapAt w q.1 k
      (Nat.succ_le_iff.mpr q.2) hq4 hk1 hk3 hrel

theorem HallNode.child_gap_le (v child : HallNode)
    (hchild : child ∈ v.children) :
    child.gapLength ≤ v.gapLength := by
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      simp only [HallNode.children, HallNode.leftChild, HallNode.rightChild,
        List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl
      · rw [HallNode.gapLength_eq_gapAt, HallNode.gapLength_eq_gapAt]
        exact gapAt_append_one_le w q1 1 (by rw [q1_val]; norm_num)
          (by omega) (by omega) (by left; exact q1_val)
      · rw [HallNode.gapLength_eq_gapAt, HallNode.gapLength_eq_gapAt]
        exact gapAt_succ_le w 1 (by omega) (by omega)
  | two =>
      simp only [HallNode.children, HallNode.leftChild, HallNode.rightChild,
        List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl
      · rw [HallNode.gapLength_eq_gapAt, HallNode.gapLength_eq_gapAt]
        exact gapAt_append_one_le w q2 2 (by rw [q2_val]; norm_num)
          (by omega) (by omega) (by left; exact q2_val)
      · rw [HallNode.gapLength_eq_gapAt, HallNode.gapLength_eq_gapAt]
        exact gapAt_succ_le w 2 (by omega) (by omega)
  | three =>
      simp only [HallNode.children, HallNode.leftChild, HallNode.rightChild,
        List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl
      · rw [HallNode.gapLength_eq_gapAt, HallNode.gapLength_eq_gapAt]
        exact gapAt_append_one_le w q3 3 (by rw [q3_val]; norm_num)
          (by omega) (by omega) (by left; exact q3_val)
      · rw [HallNode.gapLength_eq_gapAt, HallNode.gapLength_eq_gapAt]
        exact gapAt_append_one_le w q4 3 (by rw [q4_val])
          (by omega) (by omega) (by right; exact ⟨q4_val, rfl⟩)

def HallState.k : HallState → ℕ
  | .one => 1
  | .two => 2
  | .three => 3

noncomputable def HallNode.x0 (v : HallNode) : ℝ :=
  prefixMap v.word ((v.state.k : ℝ) + delta)

noncomputable def HallNode.x1 (v : HallNode) : ℝ :=
  prefixMap v.word ((v.state.k : ℝ) + epsilon)

noncomputable def HallNode.x2 (v : HallNode) : ℝ :=
  prefixMap v.word ((v.state.k : ℝ) + 1 + delta)

noncomputable def HallNode.x3 (v : HallNode) : ℝ :=
  prefixMap v.word (4 + epsilon)

theorem HallNode.interval_eq_coords (v : HallNode) :
    v.interval = Set.uIcc v.x0 v.x3 := by
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      simp only [HallNode.interval, T1, HallNode.x0, HallNode.x3, HallState.k]
      rw [eta_eq_one_add_delta, xi_eq_four_add_epsilon]
      norm_num
  | two =>
      simp only [HallNode.interval, T2, HallNode.x0, HallNode.x3, HallState.k]
      rw [prefixMap_append_xi, xi_eq_four_add_epsilon, Set.uIcc_comm]
      simp only [q2_val]
  | three =>
      simp only [HallNode.interval, T3, HallNode.x0, HallNode.x3, HallState.k]
      rw [prefixMap_append_xi, xi_eq_four_add_epsilon, Set.uIcc_comm]
      simp only [q3_val]

theorem HallNode.children_union_eq_coords (v : HallNode) :
    v.leftChild.interval ∪ v.rightChild.interval =
      Set.uIcc v.x0 v.x1 ∪ Set.uIcc v.x2 v.x3 := by
  rw [← v.interval_diff_gap, v.interval_eq_coords]
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      simp only [HallNode.gap, G1, HallNode.x0, HallNode.x1, HallNode.x2,
        HallNode.x3, HallState.k]
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      simp only [q1_val, q2_val]
      norm_num
      have h := prefixMap_interval_split w 1 (by omega) (by omega)
      norm_num at h
      exact h
  | two =>
      simp only [HallNode.gap, G2, HallNode.x0, HallNode.x1, HallNode.x2,
        HallNode.x3, HallState.k]
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      simp only [q2_val, q3_val]
      norm_num
      have h := prefixMap_interval_split w 2 (by omega) (by omega)
      norm_num at h
      exact h
  | three =>
      simp only [HallNode.gap, G3, HallNode.x0, HallNode.x1, HallNode.x2,
        HallNode.x3, HallState.k]
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      simp only [q3_val, q4_val]
      norm_num
      have h := prefixMap_interval_split w 3 (by omega) (by omega)
      norm_num at h
      exact h

theorem HallNode.gapLength_eq_coords (v : HallNode) :
    v.gapLength = |v.x2 - v.x1| := by
  rw [v.gapLength_eq_gapAt]
  rcases v with ⟨w, state⟩
  cases state <;> rfl

theorem HallNode.intervalLength_eq_coords (v : HallNode) :
    v.intervalLength = |v.x3 - v.x0| := by
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      simp only [HallNode.intervalLength, HallNode.x0, HallNode.x3, HallState.k]
      rw [eta_eq_one_add_delta, xi_eq_four_add_epsilon]
      norm_num
  | two =>
      simp only [HallNode.intervalLength, HallNode.x0, HallNode.x3, HallState.k]
      rw [prefixMap_append_xi, xi_eq_four_add_epsilon]
      simp only [q2_val]
      norm_num
      rw [abs_sub_comm]
  | three =>
      simp only [HallNode.intervalLength, HallNode.x0, HallNode.x3, HallState.k]
      rw [prefixMap_append_xi, xi_eq_four_add_epsilon]
      simp only [q3_val]
      norm_num
      rw [abs_sub_comm]

theorem HallNode.coords_order (v : HallNode) :
    (v.x0 ≤ v.x1 ∧ v.x1 ≤ v.x2 ∧ v.x2 ≤ v.x3) ∨
      (v.x3 ≤ v.x2 ∧ v.x2 ≤ v.x1 ∧ v.x1 ≤ v.x0) := by
  rcases v with ⟨w, state⟩
  cases state with
  | one => exact prefixMap_four_order w 1 (by omega) (by omega)
  | two => exact prefixMap_four_order w 2 (by omega) (by omega)
  | three => exact prefixMap_four_order w 3 (by omega) (by omega)

theorem HallNode.gap_le_intervalLength (v : HallNode) :
    v.gapLength ≤ v.intervalLength := by
  rw [v.gapLength_eq_coords, v.intervalLength_eq_coords]
  rcases v.coords_order with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h.2.1),
      abs_of_nonneg (sub_nonneg.2 (h.1.trans <| h.2.1.trans h.2.2))]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.2 h.2.1),
      abs_of_nonpos (sub_nonpos.2 (h.1.trans <| h.2.1.trans h.2.2))]
    linarith

theorem HallNode.minkowskiSum_interval_with (v u : HallNode)
    (hgap : v.gapLength ≤ u.intervalLength) :
    minkowskiSum v.interval u.interval =
      minkowskiSum (v.leftChild.interval ∪ v.rightChild.interval) u.interval := by
  rw [v.gapLength_eq_coords, u.intervalLength_eq_coords] at hgap
  rw [v.interval_eq_coords, u.interval_eq_coords,
    v.children_union_eq_coords]
  exact minkowskiSum_uIcc_split v.coords_order hgap

def nodeUnion (nodes : List HallNode) : Set ℝ :=
  ⋃ v ∈ nodes, v.interval

theorem mem_nodeUnion {nodes : List HallNode} {x : ℝ} :
    x ∈ nodeUnion nodes ↔ ∃ v ∈ nodes, x ∈ v.interval := by
  simp [nodeUnion]

theorem nodeUnion_eq_of_perm {l₁ l₂ : List HallNode} (h : l₁.Perm l₂) :
    nodeUnion l₁ = nodeUnion l₂ := by
  ext x
  simp only [mem_nodeUnion]
  constructor
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, h.mem_iff.mp hv, hx⟩
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, h.mem_iff.mpr hv, hx⟩

theorem HallNode.minkowskiSum_union_split (v : HallNode) (rest : List HallNode)
    (hrest : ∀ u ∈ rest, v.gapLength ≤ u.intervalLength) :
    let A := v.interval
    let S := v.leftChild.interval ∪ v.rightChild.interval
    let R := nodeUnion rest
    minkowskiSum (A ∪ R) (A ∪ R) =
      minkowskiSum (S ∪ R) (S ∪ R) := by
  dsimp
  let A := v.interval
  let S := v.leftChild.interval ∪ v.rightChild.interval
  let R := nodeUnion rest
  have hAA : minkowskiSum A A = minkowskiSum S S :=
    v.minkowskiSum_interval_children
  have hAR : minkowskiSum A R = minkowskiSum S R := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, y, hy, rfl⟩
      rw [mem_nodeUnion] at hy
      rcases hy with ⟨u, hu, hyu⟩
      have hsplit := v.minkowskiSum_interval_with u (hrest u hu)
      have hxy : x + y ∈ minkowskiSum A u.interval :=
        ⟨x, hx, y, hyu, rfl⟩
      rw [hsplit] at hxy
      rcases hxy with ⟨x', hx', y', hy', hsum⟩
      exact ⟨x', hx', y', mem_nodeUnion.2 ⟨u, hu, hy'⟩, hsum⟩
    · apply minkowskiSum_mono
      · change v.leftChild.interval ∪ v.rightChild.interval ⊆ v.interval
        rw [← v.interval_diff_gap]
        exact fun _ hx ↦ hx.1
      · exact fun _ h ↦ h
  have hRA : minkowskiSum R A = minkowskiSum R S := by
    rw [minkowskiSum_comm R A, minkowskiSum_comm R S, hAR]
  have hExpand :
      minkowskiSum (S ∪ R) (S ∪ R) =
        (minkowskiSum S S ∪ minkowskiSum S R) ∪
          (minkowskiSum R S ∪ minkowskiSum R R) := by
    rw [minkowskiSum_union_left S R (S ∪ R),
      minkowskiSum_union_right S S R,
      minkowskiSum_union_right R S R]
  calc
    minkowskiSum (A ∪ R) (A ∪ R) =
        (minkowskiSum A A ∪ minkowskiSum A R) ∪
          (minkowskiSum R A ∪ minkowskiSum R R) := by
            rw [minkowskiSum_union_left, minkowskiSum_union_right,
              minkowskiSum_union_right]
    _ = (minkowskiSum S S ∪ minkowskiSum S R) ∪
          (minkowskiSum R S ∪ minkowskiSum R R) := by rw [hAA, hAR, hRA]
    _ = minkowskiSum (S ∪ R) (S ∪ R) := hExpand.symm

structure WorkNode where
  node : HallNode
  remaining : ℕ
  deriving DecidableEq

def descendants (v : HallNode) : ℕ → List HallNode
  | 0 => [v]
  | n + 1 => (descendants v.leftChild n) ++ (descendants v.rightChild n)

def WorkNode.target (w : WorkNode) : List HallNode :=
  descendants w.node w.remaining

def WorkNode.work : WorkNode → ℕ
  | ⟨_, 0⟩ => 0
  | ⟨v, n + 1⟩ => 2 * WorkNode.work ⟨v, n⟩ + 1

def forestWork (forest : List WorkNode) : ℕ :=
  (forest.map WorkNode.work).sum

def forestCurrent (forest : List WorkNode) : Set ℝ :=
  nodeUnion (forest.map WorkNode.node)

def forestTarget (forest : List WorkNode) : Set ℝ :=
  nodeUnion (forest.flatMap WorkNode.target)

def ForestGood (bound : ℝ) (forest : List WorkNode) : Prop :=
  (∀ w ∈ forest, bound ≤ w.node.intervalLength) ∧
    (∀ w ∈ forest, w.remaining ≠ 0 → w.node.gapLength ≤ bound)

theorem exists_list_max {α : Type*} (f : α → ℝ) {l : List α}
    (hl : l ≠ []) :
    ∃ m ∈ l, ∀ a ∈ l, f a ≤ f m := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
      by_cases hnil : l = []
      · subst l
        exact ⟨a, by simp, by simp⟩
      · obtain ⟨m, hm, hmax⟩ := ih hnil
        by_cases ham : f a ≤ f m
        · exact ⟨m, by simp [hm], by
            intro b hb
            rcases (by simpa using hb : b = a ∨ b ∈ l) with rfl | hb
            · exact ham
            · exact hmax b hb⟩
        · have hma : f m ≤ f a := le_of_not_ge ham
          exact ⟨a, by simp, by
            intro b hb
            rcases (by simpa using hb : b = a ∨ b ∈ l) with rfl | hb
            · exact le_rfl
            · exact (hmax b hb).trans hma⟩

theorem forestWork_eq_zero_iff (forest : List WorkNode) :
    forestWork forest = 0 ↔ ∀ w ∈ forest, w.remaining = 0 := by
  induction forest with
  | nil => simp [forestWork]
  | cons w forest ih =>
      rcases w with ⟨v, remaining⟩
      cases remaining with
      | zero =>
          simpa [forestWork, WorkNode.work] using ih
      | succ n => simp [forestWork, WorkNode.work]

theorem descendants_succ (v : HallNode) (n : ℕ) :
    descendants v (n + 1) =
      (descendants v n).flatMap HallNode.children := by
  induction n generalizing v with
  | zero => simp [descendants, HallNode.children]
  | succ n ih =>
      change
        descendants v.leftChild (n + 1) ++ descendants v.rightChild (n + 1) =
          List.flatMap HallNode.children
            (descendants v.leftChild n ++ descendants v.rightChild n)
      rw [List.flatMap_append, ih, ih]

theorem descendants_eq_nodesAtLevel (n : ℕ) :
    descendants rootNode n = nodesAtLevel n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [descendants_succ, nodesAtLevel_succ, ih]

theorem mem_forestCurrent {forest : List WorkNode} {x : ℝ} :
    x ∈ forestCurrent forest ↔
      ∃ w ∈ forest, x ∈ w.node.interval := by
  simp [forestCurrent, mem_nodeUnion]

theorem forestCurrent_cons (w : WorkNode) (forest : List WorkNode) :
    forestCurrent (w :: forest) =
      w.node.interval ∪ forestCurrent forest := by
  ext x
  simp [mem_forestCurrent]

theorem forestCurrent_eq_of_perm {f₁ f₂ : List WorkNode} (h : f₁.Perm f₂) :
    forestCurrent f₁ = forestCurrent f₂ := by
  ext x
  simp only [mem_forestCurrent]
  constructor
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, h.mem_iff.mp hw, hx⟩
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, h.mem_iff.mpr hw, hx⟩

theorem forestCurrent_erase (chosen : WorkNode) {forest : List WorkNode}
    (hchosen : chosen ∈ forest) :
    forestCurrent forest =
      chosen.node.interval ∪ forestCurrent (forest.erase chosen) := by
  rw [forestCurrent_eq_of_perm (List.perm_cons_erase hchosen),
    forestCurrent_cons]

theorem forestTarget_eq_of_perm {f₁ f₂ : List WorkNode} (h : f₁.Perm f₂) :
    forestTarget f₁ = forestTarget f₂ := by
  unfold forestTarget
  apply nodeUnion_eq_of_perm
  exact h.flatMap fun _ _ ↦ List.Perm.refl _

theorem forestTarget_split {v : HallNode} {r : ℕ}
    (rest : List WorkNode) :
    forestTarget (⟨v, r + 1⟩ :: rest) =
      forestTarget (⟨v.leftChild, r⟩ :: ⟨v.rightChild, r⟩ :: rest) := by
  unfold forestTarget WorkNode.target
  simp only [List.flatMap_cons, descendants]
  ext x
  simp [nodeUnion, Set.mem_iUnion]

theorem forestTarget_erase_split {chosen : WorkNode} {forest : List WorkNode}
    (hchosen : chosen ∈ forest) {v : HallNode} {r : ℕ}
    (hchosen_eq : chosen = ⟨v, r + 1⟩) :
    forestTarget forest =
      forestTarget (⟨v.leftChild, r⟩ :: ⟨v.rightChild, r⟩ ::
        forest.erase chosen) := by
  rw [forestTarget_eq_of_perm (List.perm_cons_erase hchosen)]
  subst chosen
  exact forestTarget_split _

theorem WorkNode.work_node_irrel (v u : HallNode) (n : ℕ) :
    WorkNode.work ⟨v, n⟩ = WorkNode.work ⟨u, n⟩ := by
  induction n with
  | zero => simp [WorkNode.work]
  | succ n ih => simp [WorkNode.work, ih]

theorem forestWork_split_lt {v : HallNode} {r : ℕ}
    {chosen : WorkNode} {forest : List WorkNode}
    (hchosen : chosen ∈ forest) (hchosen_eq : chosen = ⟨v, r + 1⟩) :
    forestWork (⟨v.leftChild, r⟩ :: ⟨v.rightChild, r⟩ ::
      forest.erase chosen) < forestWork forest := by
  have hperm := (List.perm_cons_erase hchosen).map WorkNode.work
  have hsum := hperm.sum_eq
  subst chosen
  simp only [List.map_cons, List.sum_cons] at hsum
  simp only [forestWork, List.map_cons, List.sum_cons]
  have hwork_left :=
    WorkNode.work_node_irrel v.leftChild v r
  have hwork_right :=
    WorkNode.work_node_irrel v.rightChild v r
  rw [hwork_left, hwork_right]
  simp only [WorkNode.work] at hsum
  omega

theorem forestTarget_eq_current_of_zero (forest : List WorkNode)
    (hzero : ∀ w ∈ forest, w.remaining = 0) :
    forestTarget forest = forestCurrent forest := by
  unfold forestTarget forestCurrent
  congr 1
  induction forest with
  | nil => rfl
  | cons w forest ih =>
      have hw := hzero w (by simp)
      have hrest : ∀ u ∈ forest, u.remaining = 0 :=
        fun u hu ↦ hzero u (by simp [hu])
      rcases w with ⟨v, remaining⟩
      simp only at hw
      subst remaining
      simp [WorkNode.target, descendants, ih hrest]

theorem forest_refinement_sum (bound : ℝ) (forest : List WorkNode)
    (hgood : ForestGood bound forest) :
    minkowskiSum (forestCurrent forest) (forestCurrent forest) =
      minkowskiSum (forestTarget forest) (forestTarget forest) := by
  generalize hN : forestWork forest = N
  induction N using Nat.strong_induction_on generalizing bound forest with
  | h N ih =>
      by_cases hzero : N = 0
      · have hwork0 : forestWork forest = 0 := by omega
        have hallzero := (forestWork_eq_zero_iff forest).1 hwork0
        rw [forestTarget_eq_current_of_zero forest hallzero]
      · let candidates := forest.filter fun w ↦ w.remaining ≠ 0
        have hcandidates : candidates ≠ [] := by
          intro hempty
          have hallzero : ∀ w ∈ forest, w.remaining = 0 := by
            intro w hw
            by_contra hwrem
            have : w ∈ candidates := by
              simp [candidates, hw, hwrem]
            simp [hempty] at this
          have := (forestWork_eq_zero_iff forest).2 hallzero
          omega
        obtain ⟨chosen, hchosenCand, hmax⟩ :=
          exists_list_max (fun w : WorkNode ↦ w.node.gapLength) hcandidates
        have hchosen : chosen ∈ forest := by
          have hc : chosen ∈ forest ∧ chosen.remaining ≠ 0 := by
            simpa [candidates] using hchosenCand
          exact hc.1
        have hchosenRem : chosen.remaining ≠ 0 := by
          have hc : chosen ∈ forest ∧ chosen.remaining ≠ 0 := by
            simpa [candidates] using hchosenCand
          exact hc.2
        obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hchosenRem
        rcases chosen with ⟨v, remaining⟩
        simp only at hr
        subst remaining
        let newForest : List WorkNode :=
          ⟨v.leftChild, r⟩ :: ⟨v.rightChild, r⟩ ::
            forest.erase ⟨v, r + 1⟩
        have hselected_le : v.gapLength ≤ bound :=
          hgood.2 ⟨v, r + 1⟩ hchosen (by omega)
        have hnewGood : ForestGood v.gapLength newForest := by
          constructor
          · intro w hw
            simp only [newForest, List.mem_cons] at hw
            rcases hw with rfl | rfl | hw
            · exact v.children_length_ge_gap.1
            · exact v.children_length_ge_gap.2
            · exact hselected_le.trans
                (hgood.1 w (List.mem_of_mem_erase hw))
          · intro w hw hwrem
            simp only [newForest, List.mem_cons] at hw
            rcases hw with rfl | rfl | hw
            · exact v.child_gap_le v.leftChild (by simp [HallNode.children])
            · exact v.child_gap_le v.rightChild (by simp [HallNode.children])
            · apply hmax w
              simp [candidates, List.mem_of_mem_erase hw, hwrem]
        have hless : forestWork newForest < N := by
          rw [← hN]
          exact forestWork_split_lt hchosen rfl
        have hrec :
            minkowskiSum (forestCurrent newForest) (forestCurrent newForest) =
              minkowskiSum (forestTarget newForest) (forestTarget newForest) :=
          ih (forestWork newForest) hless v.gapLength newForest hnewGood rfl
        have hrest :
            ∀ u ∈ (forest.erase ⟨v, r + 1⟩).map WorkNode.node,
              v.gapLength ≤ u.intervalLength := by
          intro u hu
          simp only [List.mem_map] at hu
          rcases hu with ⟨w, hw, rfl⟩
          exact hselected_le.trans
            (hgood.1 w (List.mem_of_mem_erase hw))
        have hsplit :=
          v.minkowskiSum_union_split
            ((forest.erase ⟨v, r + 1⟩).map WorkNode.node) hrest
        have hcurrentOld :
            forestCurrent forest =
              v.interval ∪ forestCurrent (forest.erase ⟨v, r + 1⟩) :=
          forestCurrent_erase ⟨v, r + 1⟩ hchosen
        have hcurrentNew :
            forestCurrent newForest =
              (v.leftChild.interval ∪ v.rightChild.interval) ∪
                forestCurrent (forest.erase ⟨v, r + 1⟩) := by
          simp [newForest, forestCurrent_cons, Set.union_assoc]
        have htarget :
            forestTarget forest = forestTarget newForest := by
          exact forestTarget_erase_split hchosen rfl
        calc
          minkowskiSum (forestCurrent forest) (forestCurrent forest) =
              minkowskiSum
                (v.interval ∪ forestCurrent (forest.erase ⟨v, r + 1⟩))
                (v.interval ∪ forestCurrent (forest.erase ⟨v, r + 1⟩)) := by
            rw [hcurrentOld]
          _ = minkowskiSum
                ((v.leftChild.interval ∪ v.rightChild.interval) ∪
                  forestCurrent (forest.erase ⟨v, r + 1⟩))
                ((v.leftChild.interval ∪ v.rightChild.interval) ∪
                  forestCurrent (forest.erase ⟨v, r + 1⟩)) := hsplit
          _ = minkowskiSum (forestCurrent newForest) (forestCurrent newForest) := by
            rw [hcurrentNew]
          _ = minkowskiSum (forestTarget newForest) (forestTarget newForest) := hrec
          _ = minkowskiSum (forestTarget forest) (forestTarget forest) := by
            rw [htarget]

theorem cantorStage_selfSum_eq_zero (n : ℕ) :
    minkowskiSum (cantorStage n) (cantorStage n) =
      minkowskiSum (cantorStage 0) (cantorStage 0) := by
  let initial : List WorkNode := [⟨rootNode, n⟩]
  have hgood : ForestGood rootNode.gapLength initial := by
    constructor
    · intro w hw
      simp only [initial, List.mem_singleton] at hw
      subst w
      exact rootNode.gap_le_intervalLength
    · intro w hw _
      simp only [initial, List.mem_singleton] at hw
      subst w
      exact le_rfl
  have hrefine := forest_refinement_sum rootNode.gapLength initial hgood
  have hcurrent : forestCurrent initial = cantorStage 0 := by
    rw [cantorStage_zero]
    ext x
    simp [initial, forestCurrent, nodeUnion, rootNode, HallNode.interval]
  have htarget : forestTarget initial = cantorStage n := by
    unfold forestTarget initial WorkNode.target
    simp only [List.flatMap_singleton, descendants_eq_nodesAtLevel]
    rfl
  rw [hcurrent, htarget] at hrefine
  exact hrefine.symm

/-- Hall's theorem: the self-sum of `C(4)` is an interval. -/
theorem hall_C4 :
    minkowskiSum (C 4) (C 4) =
      Set.Icc (Real.sqrt 2 - 1) (4 * Real.sqrt 2 - 4) := by
  calc
    minkowskiSum (C 4) (C 4) =
        minkowskiSum (⋂ n, cantorStage n) (⋂ n, cantorStage n) := by
          rw [← C4_eq_iInter_cantorStage]
    _ = ⋂ n, minkowskiSum (cantorStage n) (cantorStage n) :=
      minkowskiSum_iInter_self cantorStage antitone_cantorStage
        cantorStage_nonempty isCompact_cantorStage
    _ = minkowskiSum (cantorStage 0) (cantorStage 0) := by
      simp_rw [cantorStage_selfSum_eq_zero]
      ext x
      simp only [Set.mem_iInter]
      constructor
      · intro hx
        exact hx 0
      · intro hx _
        exact hx
    _ = Set.Icc (Real.sqrt 2 - 1) (4 * Real.sqrt 2 - 4) := by
      rw [cantorStage_zero, T1_nil,
        minkowskiSum_Icc delta_le_epsilon delta_le_epsilon]
      congr 1 <;> simp only [delta, epsilon] <;> ring

end Cantor
end HallRay
