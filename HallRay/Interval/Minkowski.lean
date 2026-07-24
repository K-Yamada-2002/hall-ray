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

/-- Membership in a Minkowski sum, in the form most useful for proofs. -/
theorem mem_minkowskiSum {X Y : Set ℝ} {z : ℝ} :
    z ∈ minkowskiSum X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, x + y = z := by
  rfl

/-- Minkowski addition is monotone in both arguments. -/
theorem minkowskiSum_mono {X₁ X₂ Y₁ Y₂ : Set ℝ}
    (hX : X₁ ⊆ X₂) (hY : Y₁ ⊆ Y₂) :
    minkowskiSum X₁ Y₁ ⊆ minkowskiSum X₂ Y₂ := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact ⟨x, hX hx, y, hY hy, rfl⟩

theorem minkowskiSum_comm (X Y : Set ℝ) :
    minkowskiSum X Y = minkowskiSum Y X := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨y, hy, x, hx, add_comm _ _⟩
  · rintro ⟨y, hy, x, hx, rfl⟩
    exact ⟨x, hx, y, hy, add_comm _ _⟩

theorem minkowskiSum_union_left (X₁ X₂ Y : Set ℝ) :
    minkowskiSum (X₁ ∪ X₂) Y =
      minkowskiSum X₁ Y ∪ minkowskiSum X₂ Y := by
  ext z
  constructor
  · rintro ⟨x, hx | hx, y, hy, rfl⟩
    · exact Or.inl ⟨x, hx, y, hy, rfl⟩
    · exact Or.inr ⟨x, hx, y, hy, rfl⟩
  · rintro (⟨x, hx, y, hy, rfl⟩ | ⟨x, hx, y, hy, rfl⟩)
    · exact ⟨x, Or.inl hx, y, hy, rfl⟩
    · exact ⟨x, Or.inr hx, y, hy, rfl⟩

theorem minkowskiSum_union_right (X Y₁ Y₂ : Set ℝ) :
    minkowskiSum X (Y₁ ∪ Y₂) =
      minkowskiSum X Y₁ ∪ minkowskiSum X Y₂ := by
  rw [minkowskiSum_comm, minkowskiSum_union_left]
  congr 1 <;> apply minkowskiSum_comm

/-- The sum of two nonempty closed real intervals is the interval whose
endpoints are the sums of the endpoints. -/
theorem minkowskiSum_Icc {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    minkowskiSum (Set.Icc a b) (Set.Icc u v) = Set.Icc (a + u) (b + v) := by
  ext z
  constructor
  · rintro ⟨x, ⟨hax, hxb⟩, y, ⟨huy, hyv⟩, rfl⟩
    exact ⟨add_le_add hax huy, add_le_add hxb hyv⟩
  · rintro ⟨hz₁, hz₂⟩
    let x := max a (z - v)
    let y := z - x
    have hax : a ≤ x := le_max_left _ _
    have hxzv : z - v ≤ x := le_max_right _ _
    have hxb : x ≤ b := by
      apply max_le hab
      linarith
    have hyv : y ≤ v := by
      dsimp [y]
      linarith
    have huy : u ≤ y := by
      dsimp [y, x]
      have : max a (z - v) ≤ z - u :=
        max_le (by linarith) (by linarith)
      linarith
    exact ⟨x, ⟨hax, hxb⟩, y, ⟨huy, hyv⟩, by dsimp [y]; ring⟩

/--
Removing an open interval from one closed interval does not change its
Minkowski sum with a second interval whose length is at least the gap length.

This is Lemma 4.1 (`two-closed`) of `doc/main.tex`.
-/
theorem minkowskiSum_Icc_split {a b c d u v : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (huv : u ≤ v)
    (hgap : d - c ≤ v - u) :
    minkowskiSum (Set.Icc a b) (Set.Icc u v) =
      minkowskiSum (Set.Icc a c ∪ Set.Icc d b) (Set.Icc u v) := by
  rw [minkowskiSum_Icc (hac.trans <| hcd.trans hdb) huv]
  ext z
  constructor
  · intro hz
    by_cases hzc : z ≤ c + v
    · have hz' : z ∈ Set.Icc (a + u) (c + v) := ⟨hz.1, hzc⟩
      rw [← minkowskiSum_Icc hac huv] at hz'
      exact minkowskiSum_mono Set.subset_union_left (fun _ h ↦ h) hz'
    · have hdz : d + u ≤ z := by linarith
      have hz' : z ∈ Set.Icc (d + u) (b + v) := ⟨hdz, hz.2⟩
      rw [← minkowskiSum_Icc hdb huv] at hz'
      exact minkowskiSum_mono Set.subset_union_right (fun _ h ↦ h) hz'
  · intro hz
    rw [← minkowskiSum_Icc (hac.trans <| hcd.trans hdb) huv]
    apply minkowskiSum_mono ?_ (fun _ h ↦ h) hz
    rintro x (hx | hx)
    · exact ⟨hx.1, hx.2.trans (hcd.trans hdb)⟩
    · exact ⟨(hac.trans hcd).trans hx.1, hx.2⟩

/-- A finite union of closed intervals, represented by endpoint functions. -/
def intervalUnion {ι : Type*} (s : Finset ι) (l r : ι → ℝ) : Set ℝ :=
  ⋃ i ∈ s, Set.Icc (l i) (r i)

theorem mem_intervalUnion {ι : Type*} {s : Finset ι} {l r : ι → ℝ} {x : ℝ} :
    x ∈ intervalUnion s l r ↔ ∃ i ∈ s, x ∈ Set.Icc (l i) (r i) := by
  constructor
  · simp only [intervalUnion, Set.mem_iUnion]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    simp only [intervalUnion, Set.mem_iUnion]
    exact ⟨i, hi, hx.1, hx.2⟩

/-- Splitting an interval along a short gap preserves its self-sum. -/
theorem minkowskiSum_Icc_split_self {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hleft : d - c ≤ c - a) (hright : d - c ≤ b - d) :
    minkowskiSum (Set.Icc a b) (Set.Icc a b) =
      minkowskiSum (Set.Icc a c ∪ Set.Icc d b)
        (Set.Icc a c ∪ Set.Icc d b) := by
  let A := Set.Icc a b
  let L := Set.Icc a c
  let R := Set.Icc d b
  have hAB : a ≤ b := hac.trans (hcd.trans hdb)
  have hAA : minkowskiSum A A = minkowskiSum (L ∪ R) A :=
    minkowskiSum_Icc_split hac hcd hdb hAB (by linarith [hac, hcd, hdb])
  have hAL : minkowskiSum A L = minkowskiSum (L ∪ R) L :=
    minkowskiSum_Icc_split hac hcd hdb hac hleft
  have hAR : minkowskiSum A R = minkowskiSum (L ∪ R) R :=
    minkowskiSum_Icc_split hac hcd hdb hdb hright
  calc
    minkowskiSum A A = minkowskiSum (L ∪ R) A := hAA
    _ = minkowskiSum L A ∪ minkowskiSum R A := minkowskiSum_union_left _ _ _
    _ = minkowskiSum A L ∪ minkowskiSum A R := by
      rw [minkowskiSum_comm L A, minkowskiSum_comm R A]
    _ = minkowskiSum (L ∪ R) L ∪ minkowskiSum (L ∪ R) R := by
      rw [hAL, hAR]
    _ = minkowskiSum (L ∪ R) (L ∪ R) := (minkowskiSum_union_right _ _ _).symm

/--
Orientation-free version of `minkowskiSum_Icc_split_self`.  It is tailored
to continued-fraction cylinders, whose common-prefix map alternates between
increasing and decreasing.
-/
theorem minkowskiSum_uIcc_split_self {x0 x1 x2 x3 : ℝ}
    (horder :
      (x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3) ∨
      (x3 ≤ x2 ∧ x2 ≤ x1 ∧ x1 ≤ x0))
    (hleft : |x2 - x1| ≤ |x1 - x0|)
    (hright : |x2 - x1| ≤ |x3 - x2|) :
    minkowskiSum (Set.uIcc x0 x3) (Set.uIcc x0 x3) =
      minkowskiSum (Set.uIcc x0 x1 ∪ Set.uIcc x2 x3)
        (Set.uIcc x0 x1 ∪ Set.uIcc x2 x3) := by
  rcases horder with hmono | hanti
  · rw [Set.uIcc_of_le (hmono.1.trans <| hmono.2.1.trans hmono.2.2),
      Set.uIcc_of_le hmono.1, Set.uIcc_of_le hmono.2.2]
    apply minkowskiSum_Icc_split_self hmono.1 hmono.2.1 hmono.2.2
    · simpa [abs_of_nonneg (sub_nonneg.2 hmono.2.1),
        abs_of_nonneg (sub_nonneg.2 hmono.1)] using hleft
    · simpa [abs_of_nonneg (sub_nonneg.2 hmono.2.1),
        abs_of_nonneg (sub_nonneg.2 hmono.2.2)] using hright
  · rw [Set.uIcc_of_ge (hanti.1.trans <| hanti.2.1.trans hanti.2.2),
      Set.uIcc_of_ge hanti.2.2, Set.uIcc_of_ge hanti.1, Set.union_comm]
    apply minkowskiSum_Icc_split_self hanti.1 hanti.2.1 hanti.2.2
    · have hg : x1 - x2 ≤ x2 - x3 := by
        simpa [abs_of_nonpos (sub_nonpos.2 hanti.2.1),
          abs_of_nonpos (sub_nonpos.2 hanti.1)] using hright
      linarith
    · have hg : x1 - x2 ≤ x0 - x1 := by
        simpa [abs_of_nonpos (sub_nonpos.2 hanti.2.1),
          abs_of_nonpos (sub_nonpos.2 hanti.2.2)] using hleft
      linarith

/-- Orientation-free two-interval version used for cross terms in a finite
union of continued-fraction cylinders. -/
theorem minkowskiSum_uIcc_split {x0 x1 x2 x3 u v : ℝ}
    (horder :
      (x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3) ∨
      (x3 ≤ x2 ∧ x2 ≤ x1 ∧ x1 ≤ x0))
    (hgap : |x2 - x1| ≤ |v - u|) :
    minkowskiSum (Set.uIcc x0 x3) (Set.uIcc u v) =
      minkowskiSum (Set.uIcc x0 x1 ∪ Set.uIcc x2 x3) (Set.uIcc u v) := by
  rcases horder with hmono | hanti
  · rw [Set.uIcc_of_le (hmono.1.trans <| hmono.2.1.trans hmono.2.2),
      Set.uIcc_of_le hmono.1, Set.uIcc_of_le hmono.2.2]
    by_cases huv : u ≤ v
    · rw [Set.uIcc_of_le huv]
      apply minkowskiSum_Icc_split hmono.1 hmono.2.1 hmono.2.2 huv
      simpa [abs_of_nonneg (sub_nonneg.2 hmono.2.1),
        abs_of_nonneg (sub_nonneg.2 huv)] using hgap
    · have hvu : v ≤ u := le_of_not_ge huv
      rw [Set.uIcc_of_ge hvu]
      apply minkowskiSum_Icc_split hmono.1 hmono.2.1 hmono.2.2 hvu
      simpa [abs_of_nonneg (sub_nonneg.2 hmono.2.1),
        abs_of_nonpos (sub_nonpos.2 hvu)] using hgap
  · rw [Set.uIcc_of_ge (hanti.1.trans <| hanti.2.1.trans hanti.2.2),
      Set.uIcc_of_ge hanti.2.2, Set.uIcc_of_ge hanti.1, Set.union_comm]
    by_cases huv : u ≤ v
    · rw [Set.uIcc_of_le huv]
      apply minkowskiSum_Icc_split hanti.1 hanti.2.1 hanti.2.2 huv
      have hg : x1 - x2 ≤ v - u := by
        simpa [abs_of_nonpos (sub_nonpos.2 hanti.2.1),
          abs_of_nonneg (sub_nonneg.2 huv)] using hgap
      linarith
    · have hvu : v ≤ u := le_of_not_ge huv
      rw [Set.uIcc_of_ge hvu]
      apply minkowskiSum_Icc_split hanti.1 hanti.2.1 hanti.2.2 hvu
      have hg : x1 - x2 ≤ u - v := by
        simpa [abs_of_nonpos (sub_nonpos.2 hanti.2.1),
          abs_of_nonpos (sub_nonpos.2 hvu)] using hgap
      linarith

/--
Lemma 4.2 of `doc/main.tex`: if every interval in the remainder and both
pieces adjacent to a removed gap are at least as long as that gap, removing
the gap preserves the self-sum of the finite interval union.
-/
theorem minkowskiSum_union_split_self {ι : Type*}
    (s : Finset ι) (l r : ι → ℝ) {a b c d : ℝ}
    (hvalid : ∀ i ∈ s, l i ≤ r i)
    (hrest : ∀ i ∈ s, d - c ≤ r i - l i)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hleft : d - c ≤ c - a) (hright : d - c ≤ b - d) :
    let R := intervalUnion s l r
    let A := Set.Icc a b
    let S := Set.Icc a c ∪ Set.Icc d b
    minkowskiSum (A ∪ R) (A ∪ R) =
      minkowskiSum (S ∪ R) (S ∪ R) := by
  classical
  dsimp
  let Rset := intervalUnion s l r
  let A := Set.Icc a b
  let Split := Set.Icc a c ∪ Set.Icc d b
  have hAS : minkowskiSum A A = minkowskiSum Split Split :=
    minkowskiSum_Icc_split_self hac hcd hdb hleft hright
  have hAR : minkowskiSum A Rset = minkowskiSum Split Rset := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, y, hy, rfl⟩
      rw [mem_intervalUnion] at hy
      rcases hy with ⟨i, his, hyi⟩
      have hsplit := minkowskiSum_Icc_split hac hcd hdb
        (hvalid i his) (hrest i his)
      have hmem : x + y ∈ minkowskiSum A (Set.Icc (l i) (r i)) :=
        ⟨x, hx, y, hyi, rfl⟩
      rw [hsplit] at hmem
      rcases hmem with ⟨x', hx', y', hy', hxy'⟩
      exact ⟨x', hx', y', mem_intervalUnion.2 ⟨i, his, hy'⟩, hxy'⟩
    · exact minkowskiSum_mono
        (Set.union_subset
          (fun _ hx ↦ ⟨hx.1, hx.2.trans (hcd.trans hdb)⟩)
          (fun _ hx ↦ ⟨(hac.trans hcd).trans hx.1, hx.2⟩))
        (fun _ h ↦ h)
  have hRA : minkowskiSum Rset A = minkowskiSum Rset Split := by
    rw [minkowskiSum_comm Rset A, minkowskiSum_comm Rset Split, hAR]
  have hExpand :
      minkowskiSum (Split ∪ Rset) (Split ∪ Rset) =
        (minkowskiSum Split Split ∪ minkowskiSum Split Rset) ∪
          (minkowskiSum Rset Split ∪ minkowskiSum Rset Rset) := by
    rw [minkowskiSum_union_left Split Rset (Split ∪ Rset),
      minkowskiSum_union_right Split Split Rset,
      minkowskiSum_union_right Rset Split Rset]
  calc
    minkowskiSum (A ∪ Rset) (A ∪ Rset) =
        (minkowskiSum A A ∪ minkowskiSum A Rset) ∪
          (minkowskiSum Rset A ∪ minkowskiSum Rset Rset) := by
            rw [minkowskiSum_union_left, minkowskiSum_union_right,
              minkowskiSum_union_right]
    _ = (minkowskiSum Split Split ∪ minkowskiSum Split Rset) ∪
          (minkowskiSum Rset Split ∪ minkowskiSum Rset Rset) := by
            rw [hAS, hAR, hRA]
    _ = minkowskiSum (Split ∪ Rset) (Split ∪ Rset) := hExpand.symm

/--
Minkowski self-sums commute with the intersection of a decreasing sequence
of nonempty compact sets.

This is Lemma 4.3 (`sum-cap-eq-cap-sum`) of `doc/main.tex`.
-/
theorem minkowskiSum_iInter_self (K : ℕ → Set ℝ)
    (hanti : Antitone K) (_hne : ∀ n, (K n).Nonempty)
    (hcompact : ∀ n, IsCompact (K n)) :
    minkowskiSum (⋂ n, K n) (⋂ n, K n) =
      ⋂ n, minkowskiSum (K n) (K n) := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, y, hy, rfl⟩
    rw [Set.mem_iInter] at hx hy ⊢
    exact fun n ↦ ⟨x, hx n, y, hy n, rfl⟩
  · intro z hz
    let P : ℕ → Set (ℝ × ℝ) := fun n ↦
      (K n ×ˢ K n) ∩ {p | p.1 + p.2 = z}
    have hP_succ : ∀ n, P (n + 1) ⊆ P n := by
      intro n p hp
      exact ⟨⟨hanti (Nat.le_succ n) hp.1.1, hanti (Nat.le_succ n) hp.1.2⟩, hp.2⟩
    have hP_ne : ∀ n, (P n).Nonempty := by
      intro n
      have hzn : z ∈ minkowskiSum (K n) (K n) := Set.mem_iInter.mp hz n
      rcases hzn with ⟨x, hx, y, hy, hxy⟩
      exact ⟨(x, y), ⟨⟨hx, hy⟩, hxy⟩⟩
    have hP_closed : ∀ n, IsClosed (P n) := by
      intro n
      exact ((hcompact n).prod (hcompact n)).isClosed.inter
        (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)
    have hP_compact0 : IsCompact (P 0) :=
      ((hcompact 0).prod (hcompact 0)).inter_right
        (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)
    obtain ⟨p, hp⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        P hP_succ hP_ne hP_compact0 hP_closed
    have hp_all : ∀ n, p ∈ P n := Set.mem_iInter.mp hp
    refine ⟨p.1, ?_, p.2, ?_, (hp_all 0).2⟩
    · exact Set.mem_iInter.mpr fun n ↦ (hp_all n).1.1
    · exact Set.mem_iInter.mpr fun n ↦ (hp_all n).1.2

end Interval
end HallRay
