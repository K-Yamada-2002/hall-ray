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

open ContinuedFraction
open scoped Topology

private def q1 : PartialQuotient := ⟨1, by omega⟩

/-- Widely separated distinguished positions for the block construction. -/
def anchor (n : ℕ) : ℕ :=
  2 * n * n + 2 * n + 10

theorem strictMono_anchor : StrictMono anchor := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold anchor
  nlinarith

/-- The radius-`n+1` neighborhood of the `n`th distinguished position. -/
def InAnchorRegion (p n : ℕ) : Prop :=
  anchor n - (n + 1) ≤ p ∧ p ≤ anchor n + (n + 1)

theorem anchor_sub_radius (n : ℕ) :
    anchor n - (n + 1) = 2 * n * n + n + 9 := by
  simp [anchor]
  omega

theorem anchor_add_radius (n : ℕ) :
    anchor n + (n + 1) = 2 * n * n + 3 * n + 11 := by
  simp [anchor]
  ring

theorem anchor_regions_disjoint {p n m : ℕ}
    (hn : InAnchorRegion p n) (hm : InAnchorRegion p m) :
    n = m := by
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · have hsep :
        anchor n + (n + 1) < anchor m - (m + 1) := by
      rw [anchor_add_radius, anchor_sub_radius]
      nlinarith [sq_nonneg (m - n : ℤ)]
    exact False.elim ((not_lt_of_ge hn.2) (hsep.trans_le hm.1))
  · exact hnm
  · have hsep :
        anchor m + (m + 1) < anchor n - (n + 1) := by
      rw [anchor_add_radius, anchor_sub_radius]
      nlinarith [sq_nonneg (n - m : ℤ)]
    exact False.elim ((not_lt_of_ge hm.2) (hsep.trans_le hn.1))

/-- The unique owner of a position lying in an anchor region. -/
noncomputable def regionOwner (p : ℕ) (h : ∃ n, InAnchorRegion p n) : ℕ :=
  by
    classical
    exact Nat.find h

theorem regionOwner_eq {p n : ℕ} (hn : InAnchorRegion p n) :
    regionOwner p ⟨n, hn⟩ = n := by
  classical
  unfold regionOwner
  exact anchor_regions_disjoint (Nat.find_spec ⟨n, hn⟩) hn

theorem regionOwner_eq_of_mem {p n : ℕ}
    (h : ∃ m, InAnchorRegion p m) (hn : InAnchorRegion p n) :
    regionOwner p h = n := by
  classical
  unfold regionOwner
  exact anchor_regions_disjoint (Nat.find_spec h) hn

/--
The sparse two-sided sequence.  Around `anchor n`, its center is `a`, its
first `n+1` right digits come from `c`, and its first `n+1` left digits come
from `b`; all other positions are filled with `1`.
-/
noncomputable def sparseDigits
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) (p : ℕ) :
    PartialQuotient := by
  classical
  exact
    if h : ∃ n, InAnchorRegion p n then
      let n := regionOwner p h
      if p = anchor n then a
      else if anchor n < p then c (p - anchor n - 1)
      else b (anchor n - p - 1)
    else q1

noncomputable def sparseSequence
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) : BiSequence :=
  fun i ↦ if 0 ≤ i then sparseDigits a b c i.toNat else q1

theorem anchor_mem_region (n : ℕ) : InAnchorRegion (anchor n) n := by
  constructor
  · exact Nat.sub_le _ _
  · omega

theorem sparseDigits_anchor
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) (n : ℕ) :
    sparseDigits a b c (anchor n) = a := by
  classical
  rw [sparseDigits]
  split_ifs with hcenter
  · rw [regionOwner_eq_of_mem hcenter (anchor_mem_region n)]
    simp
  · exact False.elim (hcenter ⟨n, anchor_mem_region n⟩)

theorem right_position_mem_region {n k : ℕ} (hk : k ≤ n) :
    InAnchorRegion (anchor n + (k + 1)) n := by
  constructor
  · exact (Nat.sub_le _ _).trans (Nat.le_add_right _ _)
  · omega

theorem left_position_mem_region {n k : ℕ} (hk : k ≤ n) :
    InAnchorRegion (anchor n - (k + 1)) n := by
  have hrad : k + 1 ≤ n + 1 := Nat.add_le_add_right hk 1
  constructor
  · exact Nat.sub_le_sub_left hrad _
  · exact (Nat.sub_le _ _).trans (Nat.le_add_right _ _)

theorem sparseDigits_right
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) {n k : ℕ} (hk : k ≤ n) :
    sparseDigits a b c (anchor n + (k + 1)) = c k := by
  classical
  let hreg : ∃ m, InAnchorRegion (anchor n + (k + 1)) m :=
    ⟨n, right_position_mem_region hk⟩
  rw [sparseDigits, dif_pos hreg]
  rw [regionOwner_eq_of_mem hreg (right_position_mem_region hk)]
  have hright : anchor n < anchor n + (k + 1) := by omega
  simp [hright]

theorem sparseDigits_left
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) {n k : ℕ} (hk : k ≤ n) :
    sparseDigits a b c (anchor n - (k + 1)) = b k := by
  classical
  have hanchor : n + 1 < anchor n := by
    rw [anchor]
    nlinarith
  let hreg : ∃ m, InAnchorRegion (anchor n - (k + 1)) m :=
    ⟨n, left_position_mem_region hk⟩
  rw [sparseDigits, dif_pos hreg]
  rw [regionOwner_eq_of_mem hreg (left_position_mem_region hk)]
  have hcenter : anchor n - (k + 1) ≠ anchor n := by omega
  have hright : ¬anchor n < anchor n - (k + 1) := by omega
  simp [hcenter, hright]
  congr 1
  omega

theorem sparseSequence_anchor
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) (n : ℕ) :
    sparseSequence a b c (anchor n : ℤ) = a := by
  simp [sparseSequence, sparseDigits_anchor]

theorem sparseDigits_le_four_of_not_anchor
    (a : PartialQuotient) (b c : ℕ → PartialQuotient)
    (hb : ∀ n, (b n).1 ≤ 4) (hc : ∀ n, (c n).1 ≤ 4)
    {p : ℕ} (hp : ¬∃ n, p = anchor n) :
    (sparseDigits a b c p).1 ≤ 4 := by
  classical
  by_cases hreg : ∃ n, InAnchorRegion p n
  · rw [sparseDigits, dif_pos hreg]
    let n := regionOwner p hreg
    have hcenter : p ≠ anchor n := fun h ↦ hp ⟨n, h⟩
    rw [if_neg hcenter]
    split_ifs
    · exact hc _
    · exact hb _
  · rw [sparseDigits, dif_neg hreg]
    change 1 ≤ 4
    omega

theorem sparseSequence_digit_le
    (a : PartialQuotient) (b c : ℕ → PartialQuotient)
    (ha : 4 ≤ a.1) (hb : ∀ n, (b n).1 ≤ 4) (hc : ∀ n, (c n).1 ≤ 4)
    (i : ℤ) :
    (sparseSequence a b c i).1 ≤ a.1 := by
  classical
  rw [sparseSequence]
  split_ifs with hi
  · by_cases hp : ∃ n, i.toNat = anchor n
    · rcases hp with ⟨n, hn⟩
      rw [hn, sparseDigits_anchor]
    · exact (sparseDigits_le_four_of_not_anchor a b c hb hc hp).trans ha
  · change 1 ≤ a.1
    omega

theorem lambda_sparseSequence_isBounded
    (a : PartialQuotient) (b c : ℕ → PartialQuotient)
    (ha : 4 ≤ a.1) (hb : ∀ n, (b n).1 ≤ 4) (hc : ∀ n, (c n).1 ≤ 4) :
    Filter.IsBoundedUnder LE.le Filter.atTop
      (fun n : ℕ ↦ lambda (sparseSequence a b c) n) := by
  have hrange :
      BddAbove (Set.range fun n : ℕ ↦ lambda (sparseSequence a b c) n) := by
    refine ⟨(a.1 : ℝ) + 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply lambda_le_of_digits_le
    intro i
    exact_mod_cast sparseSequence_digit_le a b c ha hb hc i
  exact hrange.isBoundedUnder_of_range

theorem rightDigits_sparseSequence_anchor
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) {n k : ℕ} (hk : k ≤ n) :
    rightDigits (sparseSequence a b c) (anchor n : ℤ) k = c k := by
  unfold rightDigits sparseSequence
  rw [if_pos]
  · have hidx :
        ((anchor n : ℤ) + (k + 1 : ℕ)).toNat = anchor n + (k + 1) := by
      simpa using Int.toNat_add
        (show (0 : ℤ) ≤ (anchor n : ℕ) by positivity)
        (show (0 : ℤ) ≤ (k + 1 : ℕ) by positivity)
    rw [hidx]
    exact sparseDigits_right a b c hk
  · positivity

theorem leftDigits_sparseSequence_anchor
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) {n k : ℕ} (hk : k ≤ n) :
    leftDigits (sparseSequence a b c) (anchor n : ℤ) k = b k := by
  have hanchor : k + 1 ≤ anchor n := by
    have : n + 1 < anchor n := by
      rw [anchor]
      nlinarith
    omega
  unfold leftDigits sparseSequence
  rw [if_pos]
  · have hidx :
        ((anchor n : ℤ) - (k + 1 : ℕ)).toNat = anchor n - (k + 1) := by
      simpa using Int.toNat_sub''
        (show (0 : ℤ) ≤ (anchor n : ℕ) by positivity)
        (show (0 : ℤ) ≤ (k + 1 : ℕ) by positivity)
    rw [hidx]
    exact sparseDigits_left a b c hk
  · exact sub_nonneg.mpr (by exact_mod_cast hanchor)

theorem right_prefix_sparseSequence_anchor
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) (n : ℕ) :
    (List.range (n + 1)).map
        (rightDigits (sparseSequence a b c) (anchor n : ℤ)) =
      (List.range (n + 1)).map c := by
  apply List.map_congr_left
  intro k hk
  exact rightDigits_sparseSequence_anchor a b c (Nat.lt_succ_iff.mp (List.mem_range.mp hk))

theorem left_prefix_sparseSequence_anchor
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) (n : ℕ) :
    (List.range (n + 1)).map
        (leftDigits (sparseSequence a b c) (anchor n : ℤ)) =
      (List.range (n + 1)).map b := by
  apply List.map_congr_left
  intro k hk
  exact leftDigits_sparseSequence_anchor a b c (Nat.lt_succ_iff.mp (List.mem_range.mp hk))

theorem lambda_sparseSequence_anchor_error
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) (n : ℕ) :
    |lambda (sparseSequence a b c) (anchor n : ℤ) -
        ((a.1 : ℝ) + value 0 c + value 0 b)| ≤
      2 / 4 ^ ((n + 1) / 2) := by
  have hr := abs_value_zero_sub_le_of_common_prefix
    (rightDigits (sparseSequence a b c) (anchor n : ℤ)) c (n + 1)
    (right_prefix_sparseSequence_anchor a b c n)
  have hl := abs_value_zero_sub_le_of_common_prefix
    (leftDigits (sparseSequence a b c) (anchor n : ℤ)) b (n + 1)
    (left_prefix_sparseSequence_anchor a b c n)
  rw [lambda_eq_center_add_tails, sparseSequence_anchor]
  calc
    |↑a + value 0 (rightDigits (sparseSequence a b c) ↑(anchor n)) +
          value 0 (leftDigits (sparseSequence a b c) ↑(anchor n)) -
        (↑a + value 0 c + value 0 b)| =
        |(value 0 (rightDigits (sparseSequence a b c) ↑(anchor n)) - value 0 c) +
          (value 0 (leftDigits (sparseSequence a b c) ↑(anchor n)) - value 0 b)| := by
            congr 1
            ring
    _ ≤ |value 0 (rightDigits (sparseSequence a b c) ↑(anchor n)) - value 0 c| +
          |value 0 (leftDigits (sparseSequence a b c) ↑(anchor n)) - value 0 b| :=
      abs_add_le _ _
    _ ≤ 1 / 4 ^ ((n + 1) / 2) + 1 / 4 ^ ((n + 1) / 2) :=
      add_le_add hr hl
    _ = 2 / 4 ^ ((n + 1) / 2) := by ring

theorem tendsto_anchor_even :
    Filter.Tendsto (fun n : ℕ ↦ anchor (2 * n)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro N
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hself : 2 * n ≤ anchor (2 * n) := by
    unfold anchor
    omega
  omega

theorem tendsto_lambda_sparseSequence_anchor_even
    (a : PartialQuotient) (b c : ℕ → PartialQuotient) :
    Filter.Tendsto
      (fun n : ℕ ↦ lambda (sparseSequence a b c) (anchor (2 * n) : ℤ))
      Filter.atTop (𝓝 ((a.1 : ℝ) + value 0 c + value 0 b)) := by
  apply tendsto_iff_dist_tendsto_zero.2
  let ell : ℝ := (a.1 : ℝ) + value 0 c + value 0 b
  let err : ℕ → ℝ := fun n ↦ 2 * (1 / 4 : ℝ) ^ n
  have herr : ∀ n,
      dist (lambda (sparseSequence a b c) (anchor (2 * n) : ℤ)) ell ≤ err n := by
    intro n
    have h := lambda_sparseSequence_anchor_error a b c (2 * n)
    have hlen : (2 * n + 1) / 2 = n := by omega
    simpa [ell, err, Real.dist_eq, hlen, ← one_div_pow, div_eq_mul_inv] using h
  apply squeeze_zero (fun _ ↦ dist_nonneg) herr
  simpa [err] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).const_mul (2 : ℝ)

theorem eventually_lambda_sparseSequence_lt_add
    (a : PartialQuotient) (b c : ℕ → PartialQuotient)
    (hb : ∀ n, (b n).1 ≤ 4) (hc : ∀ n, (c n).1 ≤ 4)
    (hell : 6 ≤ (a.1 : ℝ) + value 0 c + value 0 b)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in Filter.atTop,
      lambda (sparseSequence a b c) p <
        (a.1 : ℝ) + value 0 c + value 0 b + ε := by
  let ell : ℝ := (a.1 : ℝ) + value 0 c + value 0 b
  have herr_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ 2 * (1 / 4 : ℝ) ^ n)
        Filter.atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).const_mul (2 : ℝ)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 2 * (1 / 4 : ℝ) ^ n < ε :=
    herr_tendsto.eventually (Iio_mem_nhds hε)
  rcases Filter.eventually_atTop.1 hev with ⟨K, hK⟩
  filter_upwards [Filter.eventually_ge_atTop (anchor (2 * K))] with p hp
  by_cases hpa : ∃ m, p = anchor m
  · rcases hpa with ⟨m, rfl⟩
    have h2Km : 2 * K ≤ m :=
      strictMono_anchor.le_iff_le.mp hp
    have hKm : K ≤ (m + 1) / 2 := by omega
    have hpow :
        1 / (4 : ℝ) ^ ((m + 1) / 2) ≤ 1 / 4 ^ K :=
      one_div_pow_le_one_div_pow_of_le (by norm_num) hKm
    have herr := lambda_sparseSequence_anchor_error a b c m
    have habove :
        lambda (sparseSequence a b c) (anchor m : ℤ) - ell ≤
          2 / 4 ^ ((m + 1) / 2) :=
      (le_abs_self _).trans herr
    have hsmall : 2 / (4 : ℝ) ^ K < ε := by
      simpa [← one_div_pow, div_eq_mul_inv] using hK K le_rfl
    have herrmono :
        2 / (4 : ℝ) ^ ((m + 1) / 2) ≤ 2 / 4 ^ K := by
      calc
        2 / (4 : ℝ) ^ ((m + 1) / 2) =
            2 * (1 / 4 ^ ((m + 1) / 2)) := by ring
        _ ≤ 2 * (1 / 4 ^ K) := mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ = 2 / 4 ^ K := by ring
    dsimp [ell] at habove ⊢
    nlinarith
  · have hcenterNat :
        (sparseDigits a b c p).1 ≤ 4 :=
      sparseDigits_le_four_of_not_anchor a b c hb hc hpa
    have hcenter :
        (((sparseSequence a b c) (p : ℤ)).1 : ℝ) ≤ 4 := by
      have hcR : (((sparseDigits a b c p).1 : ℕ) : ℝ) ≤ 4 := by
        exact_mod_cast hcenterNat
      simpa [sparseSequence] using hcR
    have hlam := (lambda_mem_Icc (sparseSequence a b c) (p : ℤ)).2
    nlinarith

/--
Analytic limsup criterion used by the block construction: an unbounded
subsequence converging to `ell`, together with an eventual upper bound by
`ell + ε`, forces the Lagrange value to equal `ell`.
-/
theorem lagrangeValue_eq_of_tendsto_subsequence
    (A : BiSequence) (ell : ℝ) (j : ℕ → ℕ)
    (hbdd : Filter.IsBoundedUnder LE.le Filter.atTop
      (fun n : ℕ ↦ lambda A n))
    (hj : Filter.Tendsto j Filter.atTop Filter.atTop)
    (hsub : Filter.Tendsto (fun n ↦ lambda A (j n)) Filter.atTop (𝓝 ell))
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop, lambda A n < ell + ε) :
    lagrangeValue A = ell := by
  have hcob := lambda_isCobounded A
  apply le_antisymm
  · rw [lagrangeValue, Filter.limsup_le_iff hcob hbdd]
    intro y hy
    simpa [show ell + (y - ell) = y by ring] using hupper (y - ell) (sub_pos.2 hy)
  · rw [lagrangeValue, Filter.le_limsup_iff hcob hbdd]
    intro y hy
    have hsub_y : ∀ᶠ n : ℕ in Filter.atTop, y < lambda A (j n) :=
      hsub.eventually (Ioi_mem_nhds hy)
    rw [Filter.frequently_atTop]
    intro N
    have hjN : ∀ᶠ n : ℕ in Filter.atTop, N ≤ j n :=
      (Filter.tendsto_atTop.1 hj N)
    obtain ⟨n, hnN, hny⟩ := (hjN.and hsub_y).exists
    exact ⟨j n, hnN, hny⟩

/-- The sparse block sequence realizes `a + [0;c…] + [0;b…]`. -/
theorem large_value_mem_spectrum
    (a : PartialQuotient) (b c : ℕ → PartialQuotient)
    (ha : 5 ≤ a.1) (hb : ∀ n, (b n).1 ≤ 4) (hc : ∀ n, (c n).1 ≤ 4)
    (hell : 6 ≤ (a.1 : ℝ) + value 0 c + value 0 b) :
    (a.1 : ℝ) + value 0 c + value 0 b ∈ spectrum := by
  let A := sparseSequence a b c
  have hbdd :
      Filter.IsBoundedUnder LE.le Filter.atTop (fun n : ℕ ↦ lambda A n) :=
    lambda_sparseSequence_isBounded a b c (by omega) hb hc
  have hval :
      lagrangeValue A = (a.1 : ℝ) + value 0 c + value 0 b := by
    apply lagrangeValue_eq_of_tendsto_subsequence A
      ((a.1 : ℝ) + value 0 c + value 0 b) (fun n ↦ anchor (2 * n)) hbdd
    · exact tendsto_anchor_even
    · exact tendsto_lambda_sparseSequence_anchor_even a b c
    · intro ε hε
      exact eventually_lambda_sparseSequence_lt_add a b c hb hc hell hε
  exact ⟨A, hbdd, hval.symm⟩

end Lagrange
end HallRay
