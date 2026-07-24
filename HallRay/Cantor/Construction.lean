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
open scoped Topology

def q1 : PartialQuotient := ⟨1, by omega⟩
def q2 : PartialQuotient := ⟨2, by omega⟩
def q3 : PartialQuotient := ⟨3, by omega⟩
def q4 : PartialQuotient := ⟨4, by omega⟩

@[simp] theorem q1_val : q1.1 = 1 := rfl
@[simp] theorem q2_val : q2.1 = 2 := rfl
@[simp] theorem q3_val : q3.1 = 3 := rfl
@[simp] theorem q4_val : q4.1 = 4 := rfl

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

/-- The small complete-quotient tail `δ = (√2 - 1) / 2`. -/
noncomputable def delta : ℝ :=
  (Real.sqrt 2 - 1) / 2

/-- The large complete-quotient tail `ε = 2(√2 - 1)`. -/
noncomputable def epsilon : ℝ :=
  2 * (Real.sqrt 2 - 1)

theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  norm_num

theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)

theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  nlinarith [sqrt_two_sq, sqrt_two_pos]

theorem sqrt_two_lt_two : Real.sqrt 2 < (2 : ℝ) := by
  nlinarith [sqrt_two_sq, sqrt_two_pos]

theorem delta_pos : 0 < delta := by
  unfold delta
  linarith [one_lt_sqrt_two]

theorem epsilon_pos : 0 < epsilon := by
  unfold epsilon
  linarith [one_lt_sqrt_two]

theorem epsilon_le_one : epsilon ≤ 1 := by
  unfold epsilon
  nlinarith [sqrt_two_sq, sqrt_two_pos]

theorem one_div_xi : 1 / xi = delta := by
  have hxi : xi ≠ 0 := by
    unfold xi
    positivity
  apply (div_eq_iff hxi).2
  unfold xi delta
  nlinarith [sqrt_two_sq]

theorem one_div_eta : 1 / eta = epsilon := by
  have heta : eta ≠ 0 := by
    unfold eta
    positivity
  apply (div_eq_iff heta).2
  unfold eta epsilon
  nlinarith [sqrt_two_sq]

theorem delta_le_epsilon : delta ≤ epsilon := by
  unfold delta epsilon
  linarith [one_lt_sqrt_two]

theorem eta_eq_one_add_delta : eta = 1 + delta := by
  unfold eta delta
  ring

theorem xi_eq_four_add_epsilon : xi = 4 + epsilon := by
  unfold xi epsilon
  ring

theorem one_div_four_add_epsilon : 1 / (4 + epsilon) = delta := by
  rw [← xi_eq_four_add_epsilon, one_div_xi]

theorem one_div_one_add_delta : 1 / (1 + delta) = epsilon := by
  rw [← eta_eq_one_add_delta, one_div_eta]

/-- The interval `[δ, ε]` is invariant under every allowed tail step. -/
theorem tailStep_mem_delta_epsilon (a : PartialQuotient)
    (ha : a.1 ≤ 4) {x : ℝ} (hx : x ∈ Set.Icc delta epsilon) :
    1 / ((a.1 : ℝ) + x) ∈ Set.Icc delta epsilon := by
  have ha1 : (1 : ℝ) ≤ a.1 := one_le_partialQuotient a
  have ha4 : (a.1 : ℝ) ≤ 4 := by exact_mod_cast ha
  have hden : 0 < (a.1 : ℝ) + x := by
    linarith [delta_pos, hx.1]
  constructor
  · rw [← one_div_four_add_epsilon]
    exact one_div_le_one_div_of_le hden (by linarith [hx.2])
  · rw [← one_div_one_add_delta]
    exact one_div_le_one_div_of_le (by linarith [delta_pos])
      (by linarith [hx.1])

/-- Allowed finite words preserve Hall's invariant tail interval. -/
theorem tailMap_mem_delta_epsilon (w : Word)
    (hw : ∀ a ∈ w, a.1 ≤ 4) {x : ℝ}
    (hx : x ∈ Set.Icc delta epsilon) :
    tailMap w x ∈ Set.Icc delta epsilon := by
  induction w generalizing x with
  | nil => simpa
  | cons a w ih =>
      rw [tailMap_cons]
      apply tailStep_mem_delta_epsilon a (hw a (by simp))
      exact ih (fun b hb ↦ hw b (by simp [hb])) hx

/-- Values whose digits are at most four lie in the initial Hall interval. -/
theorem value_mem_delta_epsilon (digits : ℕ → PartialQuotient)
    (hdigits : ∀ n, (digits n).1 ≤ 4) :
    value 0 digits ∈ Set.Icc delta epsilon := by
  let approximant : ℕ → ℝ :=
    fun n ↦ tailMap ((List.range n).map digits) delta
  have happ_mem : ∀ n, approximant n ∈ Set.Icc delta epsilon := by
    intro n
    apply tailMap_mem_delta_epsilon
    · intro a ha
      simp only [List.mem_map, List.mem_range] at ha
      rcases ha with ⟨i, _, rfl⟩
      exact hdigits i
    · exact ⟨le_rfl, delta_le_epsilon⟩
  have happ_tendsto : Filter.Tendsto approximant Filter.atTop (𝓝 (value 0 digits)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hpow : Filter.Tendsto (fun k : ℕ ↦ ((1 / 4 : ℝ) ^ k))
        Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hev : ∀ᶠ k : ℕ in Filter.atTop, (1 / 4 : ℝ) ^ k < ε :=
      hpow.eventually (Iio_mem_nhds hε)
    rcases Filter.eventually_atTop.1 hev with ⟨k, hk⟩
    refine ⟨2 * k, fun n hn ↦ ?_⟩
    have hkn : k ≤ n / 2 := by omega
    have hpow_le : (1 / 4 : ℝ) ^ (n / 2) ≤ (1 / 4 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkn
    have hcyl :=
      abs_value_zero_sub_tailMap_prefix_le digits n
        (show delta ∈ Set.Icc (0 : ℝ) 1 by
          constructor
          · exact delta_pos.le
          · unfold delta
            linarith [sqrt_two_lt_two])
    have hbound : 1 / (4 : ℝ) ^ (n / 2) < ε := by
      rw [← one_div_pow]
      exact lt_of_le_of_lt hpow_le (hk k le_rfl)
    rw [Real.dist_eq]
    dsimp [approximant]
    rw [abs_sub_comm]
    exact hcyl.trans_lt hbound
  exact isClosed_Icc.mem_of_tendsto happ_tendsto
    (Filter.Eventually.of_forall happ_mem)

/-- A convenient compact alphabet for the four allowed partial quotients. -/
abbrev Digit4 := Fin 4

def digit4PartialQuotient (a : Digit4) : PartialQuotient :=
  ⟨a.1 + 1, by omega⟩

@[simp]
theorem digit4PartialQuotient_val (a : Digit4) :
    (digit4PartialQuotient a).1 = a.1 + 1 := rfl

noncomputable def digit4Value (digits : ℕ → Digit4) : ℝ :=
  value 0 (fun n ↦ digit4PartialQuotient (digits n))

/-- The value map on four-letter digit streams is continuous. -/
theorem continuous_digit4Value : Continuous digit4Value := by
  rw [continuous_iff_continuousAt]
  intro digits
  apply Metric.continuousAt_iff'.2
  intro ε hε
  have hpow : Filter.Tendsto (fun k : ℕ ↦ ((1 / 4 : ℝ) ^ k))
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ k : ℕ in Filter.atTop, (1 / 4 : ℝ) ^ k < ε / 2 :=
    hpow.eventually (Iio_mem_nhds (by positivity))
  rcases Filter.eventually_atTop.1 hev with ⟨k, hk⟩
  let n := 2 * k
  have hpref :
      ∀ᶠ other : ℕ → Digit4 in 𝓝 digits,
        ∀ i ∈ Finset.range n, other i = digits i := by
    apply (Finset.range n).eventually_all.2
    intro i _
    exact (continuous_apply i).continuousAt
      ((isOpen_discrete {digits i}).mem_nhds (Set.mem_singleton _))
  filter_upwards [hpref] with other hother
  let ds : ℕ → PartialQuotient :=
    fun i ↦ digit4PartialQuotient (digits i)
  let os : ℕ → PartialQuotient :=
    fun i ↦ digit4PartialQuotient (other i)
  have hwords :
      (List.range n).map os = (List.range n).map ds := by
    apply List.map_congr_left
    intro i hi
    exact congrArg digit4PartialQuotient
      (hother i (by simpa using hi))
  have hconv : convergent 0 os n = convergent 0 ds n := by
    simp only [convergent, hwords]
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hos := abs_value_zero_sub_tailMap_prefix_le os n hzero
  have hds := abs_value_zero_sub_tailMap_prefix_le ds n hzero
  have hn : n / 2 = k := by simp [n]
  have hsmall : 1 / (4 : ℝ) ^ (n / 2) < ε / 2 := by
    rw [hn, ← one_div_pow]
    exact hk k le_rfl
  rw [Real.dist_eq]
  change |value 0 os - value 0 ds| < ε
  have hconv_os :
      tailMap ((List.range n).map os) 0 = convergent 0 os n := by
    simp [convergent, finiteValue, finiteTail]
  have hconv_ds :
      tailMap ((List.range n).map ds) 0 = convergent 0 ds n := by
    simp [convergent, finiteValue, finiteTail]
  rw [hconv_os] at hos
  rw [hconv_ds] at hds
  rw [hconv] at hos
  calc
    |value 0 os - value 0 ds| ≤
        |value 0 os - convergent 0 ds n| +
          |convergent 0 ds n - value 0 ds| := abs_sub_le _ _ _
    _ < ε := by
      have hds' :
          |convergent 0 ds n - value 0 ds| ≤ 1 / 4 ^ (n / 2) := by
        simpa only [abs_sub_comm] using hds
      linarith

/-- `C(4)` is exactly the range of the compact four-letter stream space. -/
theorem C4_eq_range : C 4 = Set.range digit4Value := by
  ext x
  constructor
  · rintro ⟨digits, hdigits, rfl⟩
    let encoded : ℕ → Digit4 :=
      fun n ↦ ⟨(digits n).1 - 1, by
        have hpos := (digits n).2
        have hle := hdigits n
        omega⟩
    refine ⟨encoded, ?_⟩
    unfold digit4Value
    congr 2
    funext n
    apply Subtype.ext
    dsimp [encoded, digit4PartialQuotient]
    have hnpos := (digits n).2
    omega
  · rintro ⟨digits, rfl⟩
    refine ⟨fun n ↦ digit4PartialQuotient (digits n), ?_, rfl⟩
    intro n
    simp only [digit4PartialQuotient_val]
    omega

theorem isCompact_C4 : IsCompact (C 4) := by
  rw [C4_eq_range, ← Set.image_univ]
  exact isCompact_univ.image continuous_digit4Value

theorem isClosed_C4 : IsClosed (C 4) := isCompact_C4.isClosed

/-- The interval `T₁(w)` from §2.2 of `doc/main.tex`. -/
noncomputable def T1 (w : Word) : Set ℝ :=
  Set.uIcc (prefixMap w eta) (prefixMap w xi)

/-- The interval `T₂(w)` from §2.2 of `doc/main.tex`. -/
noncomputable def T2 (w : Word) : Set ℝ :=
  Set.uIcc (prefixMap w xi) (prefixMap (w ++ [q2]) xi)

/-- The interval `T₃(w)` from §2.2 of `doc/main.tex`. -/
noncomputable def T3 (w : Word) : Set ℝ :=
  Set.uIcc (prefixMap w xi) (prefixMap (w ++ [q3]) xi)

/-- A bounded digit stream with a prescribed prefix lies in the corresponding
state-`T₁` cylinder. -/
theorem value_mem_T1_of_prefix (digits : ℕ → PartialQuotient)
    (hdigits : ∀ n, (digits n).1 ≤ 4) (w : Word)
    (hpref : (List.range w.length).map digits = w) :
    value 0 digits ∈ T1 w := by
  rw [value_zero_eq_tailMap_prefix digits w.length, hpref]
  unfold T1
  rw [prefixMap_eq_tailMap, prefixMap_eq_tailMap, one_div_eta, one_div_xi]
  rw [Set.uIcc_comm]
  apply tailMap_mem_uIcc delta_pos.le delta_le_epsilon epsilon_le_one
  exact value_mem_delta_epsilon _ (fun n ↦ hdigits (w.length + n))

/-- State `T₂(w)` consists of bounded continuations whose next digit is at
least two. -/
theorem value_mem_T2_of_prefix (digits : ℕ → PartialQuotient)
    (hdigits : ∀ n, (digits n).1 ≤ 4) (w : Word)
    (hpref : (List.range w.length).map digits = w)
    (hnext : 2 ≤ (digits w.length).1) :
    value 0 digits ∈ T2 w := by
  let shifted : ℕ → PartialQuotient := fun n ↦ digits (w.length + n)
  have htail := value_mem_delta_epsilon shifted
    (fun n ↦ hdigits (w.length + n))
  have htail2 := value_mem_delta_epsilon (fun n ↦ shifted (1 + n))
    (fun n ↦ hdigits (w.length + (1 + n)))
  have hrec := value_zero_eq_tailMap_prefix shifted 1
  have hshift :
      value 0 shifted =
        1 / ((digits w.length).1 + value 0 (fun n ↦ shifted (1 + n))) := by
    simpa [shifted, add_assoc] using hrec
  have hupper :
      value 0 shifted ≤ 1 / ((2 : ℝ) + delta) := by
    rw [hshift]
    apply one_div_le_one_div_of_le (by linarith [delta_pos])
    have hnextR : (2 : ℝ) ≤ (digits w.length).1 := by exact_mod_cast hnext
    linarith [htail2.1]
  have hbeta :
      tailMap [q2] delta = 1 / ((2 : ℝ) + delta) := by
    simp only [tailMap_cons, tailMap_nil, q2_val]
    norm_num
  rw [value_zero_eq_tailMap_prefix digits w.length, hpref]
  unfold T2
  rw [prefixMap_eq_tailMap, prefixMap_eq_tailMap, one_div_xi,
    tailMap_append]
  apply tailMap_mem_uIcc delta_pos.le
  · rw [hbeta]
    exact htail.1.trans hupper
  · rw [hbeta]
    apply (div_le_iff₀ (by linarith [delta_pos] : (0 : ℝ) < 2 + delta)).2
    linarith [delta_pos]
  · exact ⟨htail.1, by simpa [hbeta] using hupper⟩

/-- State `T₃(w)` consists of bounded continuations whose next digit is at
least three. -/
theorem value_mem_T3_of_prefix (digits : ℕ → PartialQuotient)
    (hdigits : ∀ n, (digits n).1 ≤ 4) (w : Word)
    (hpref : (List.range w.length).map digits = w)
    (hnext : 3 ≤ (digits w.length).1) :
    value 0 digits ∈ T3 w := by
  let shifted : ℕ → PartialQuotient := fun n ↦ digits (w.length + n)
  have htail := value_mem_delta_epsilon shifted
    (fun n ↦ hdigits (w.length + n))
  have htail2 := value_mem_delta_epsilon (fun n ↦ shifted (1 + n))
    (fun n ↦ hdigits (w.length + (1 + n)))
  have hrec := value_zero_eq_tailMap_prefix shifted 1
  have hshift :
      value 0 shifted =
        1 / ((digits w.length).1 + value 0 (fun n ↦ shifted (1 + n))) := by
    simpa [shifted, add_assoc] using hrec
  have hupper :
      value 0 shifted ≤ 1 / ((3 : ℝ) + delta) := by
    rw [hshift]
    apply one_div_le_one_div_of_le (by linarith [delta_pos])
    have hnextR : (3 : ℝ) ≤ (digits w.length).1 := by exact_mod_cast hnext
    linarith [htail2.1]
  have hbeta :
      tailMap [q3] delta = 1 / ((3 : ℝ) + delta) := by
    simp only [tailMap_cons, tailMap_nil, q3_val]
    norm_num
  rw [value_zero_eq_tailMap_prefix digits w.length, hpref]
  unfold T3
  rw [prefixMap_eq_tailMap, prefixMap_eq_tailMap, one_div_xi,
    tailMap_append]
  apply tailMap_mem_uIcc delta_pos.le
  · rw [hbeta]
    exact htail.1.trans hupper
  · rw [hbeta]
    apply (div_le_iff₀ (by linarith [delta_pos] : (0 : ℝ) < 3 + delta)).2
    linarith [delta_pos]
  · exact ⟨htail.1, by simpa [hbeta] using hupper⟩

/-- The open gap `G₁(w)` removed from `T₁(w)`. -/
noncomputable def G1 (w : Word) : Set ℝ :=
  Set.uIoo (prefixMap (w ++ [q1]) eta) (prefixMap (w ++ [q2]) xi)

/-- The open gap `G₂(w)` removed from `T₂(w)`. -/
noncomputable def G2 (w : Word) : Set ℝ :=
  Set.uIoo (prefixMap (w ++ [q2]) eta) (prefixMap (w ++ [q3]) xi)

/-- The open gap `G₃(w)` removed from `T₃(w)`. -/
noncomputable def G3 (w : Word) : Set ℝ :=
  Set.uIoo (prefixMap (w ++ [q3]) eta) (prefixMap (w ++ [q4]) xi)

/-- The three interval states in Hall's recursive construction. -/
inductive HallState
  | one
  | two
  | three
  deriving DecidableEq, Repr

/-- A node records the already fixed continued-fraction word and its state. -/
structure HallNode where
  word : Word
  state : HallState
  deriving DecidableEq, Repr

noncomputable def HallNode.interval (v : HallNode) : Set ℝ :=
  match v.state with
  | .one => T1 v.word
  | .two => T2 v.word
  | .three => T3 v.word

noncomputable def HallNode.gap (v : HallNode) : Set ℝ :=
  match v.state with
  | .one => G1 v.word
  | .two => G2 v.word
  | .three => G3 v.word

/-- Left child in Equation (2.2) of `doc/main.tex`. -/
def HallNode.leftChild (v : HallNode) : HallNode :=
  match v.state with
  | .one => ⟨v.word ++ [q1], .one⟩
  | .two => ⟨v.word ++ [q2], .one⟩
  | .three => ⟨v.word ++ [q3], .one⟩

/-- Right child in Equation (2.2) of `doc/main.tex`. -/
def HallNode.rightChild (v : HallNode) : HallNode :=
  match v.state with
  | .one => ⟨v.word, .two⟩
  | .two => ⟨v.word, .three⟩
  | .three => ⟨v.word ++ [q4], .one⟩

def HallNode.children (v : HallNode) : List HallNode :=
  [v.leftChild, v.rightChild]

def rootNode : HallNode := ⟨[], .one⟩

/-- Position of a bounded digit stream in the three-state binary refinement. -/
structure GuidedPosition where
  node : HallNode
  consumed : ℕ

def guidedStep (digits : ℕ → PartialQuotient) (p : GuidedPosition) :
    GuidedPosition :=
  match p.node.state with
  | .one =>
      if (digits p.consumed).1 = 1 then
        ⟨p.node.leftChild, p.consumed + 1⟩
      else
        ⟨p.node.rightChild, p.consumed⟩
  | .two =>
      if (digits p.consumed).1 = 2 then
        ⟨p.node.leftChild, p.consumed + 1⟩
      else
        ⟨p.node.rightChild, p.consumed⟩
  | .three =>
      if (digits p.consumed).1 = 3 then
        ⟨p.node.leftChild, p.consumed + 1⟩
      else
        ⟨p.node.rightChild, p.consumed + 1⟩

def guidedPosition (digits : ℕ → PartialQuotient) : ℕ → GuidedPosition
  | 0 => ⟨rootNode, 0⟩
  | n + 1 => guidedStep digits (guidedPosition digits n)

/-- Nodes after `n` simultaneous recursive subdivisions. -/
def nodesAtLevel : ℕ → List HallNode
  | 0 => [rootNode]
  | n + 1 => (nodesAtLevel n).flatMap HallNode.children

/-- The finite closed union remaining at a fixed recursive depth. -/
noncomputable def cantorStage (n : ℕ) : Set ℝ :=
  ⋃ v ∈ nodesAtLevel n, v.interval

@[simp]
theorem nodesAtLevel_zero : nodesAtLevel 0 = [rootNode] := rfl

@[simp]
theorem nodesAtLevel_succ (n : ℕ) :
    nodesAtLevel (n + 1) = (nodesAtLevel n).flatMap HallNode.children := rfl

theorem cantorStage_zero : cantorStage 0 = T1 [] := by
  simp [cantorStage, rootNode, HallNode.interval]

theorem guidedPosition_mem_nodesAtLevel (digits : ℕ → PartialQuotient) (n : ℕ) :
    (guidedPosition digits n).node ∈ nodesAtLevel n := by
  induction n with
  | zero => simp [guidedPosition, nodesAtLevel, rootNode]
  | succ n ih =>
      simp only [guidedPosition, nodesAtLevel_succ, List.mem_flatMap]
      refine ⟨(guidedPosition digits n).node, ih, ?_⟩
      rcases guidedPosition digits n with ⟨⟨w, state⟩, consumed⟩
      cases state <;> simp [guidedStep, HallNode.children] <;> split <;> simp

/-- The guided automaton records precisely the already consumed prefix and
the lower-bound invariant encoded by its current state. -/
theorem guidedPosition_invariant (digits : ℕ → PartialQuotient)
    (hdigits : ∀ n, (digits n).1 ≤ 4) (n : ℕ) :
    (List.range (guidedPosition digits n).consumed).map digits =
        (guidedPosition digits n).node.word ∧
      match (guidedPosition digits n).node.state with
      | .one => True
      | .two => 2 ≤ (digits (guidedPosition digits n).consumed).1
      | .three => 3 ≤ (digits (guidedPosition digits n).consumed).1 := by
  induction n with
  | zero => simp [guidedPosition, rootNode]
  | succ n ih =>
      rcases hp : guidedPosition digits n with ⟨⟨w, state⟩, consumed⟩
      rw [hp] at ih
      simp only at ih
      cases state with
      | one =>
          by_cases hdigit : (digits consumed).1 = 1
          · have hq : digits consumed = q1 := by
              apply Subtype.ext
              change (digits consumed).1 = q1.1
              rw [q1_val]
              exact hdigit
            simp only [guidedPosition, hp, guidedStep, hdigit, if_pos,
              HallNode.leftChild]
            constructor
            · rw [List.range_succ, List.map_append, ih.1]
              simp [hq]
            · trivial
          · have htwo : 2 ≤ (digits consumed).1 := by
              have hpos := (digits consumed).2
              omega
            simp [guidedPosition, hp, guidedStep, hdigit, ih.1, htwo,
              HallNode.rightChild]
      | two =>
          have htwo := ih.2
          by_cases hdigit : (digits consumed).1 = 2
          · have hq : digits consumed = q2 := by
              apply Subtype.ext
              change (digits consumed).1 = q2.1
              rw [q2_val]
              exact hdigit
            simp only [guidedPosition, hp, guidedStep, hdigit, if_pos,
              HallNode.leftChild]
            constructor
            · rw [List.range_succ, List.map_append, ih.1]
              simp [hq]
            · trivial
          · have hthree : 3 ≤ (digits consumed).1 := by omega
            simp [guidedPosition, hp, guidedStep, hdigit, ih.1, hthree,
              HallNode.rightChild]
      | three =>
          have hthree := ih.2
          by_cases hdigit : (digits consumed).1 = 3
          · have hq : digits consumed = q3 := by
              apply Subtype.ext
              change (digits consumed).1 = q3.1
              rw [q3_val]
              exact hdigit
            simp only [guidedPosition, hp, guidedStep, hdigit, if_pos,
              HallNode.leftChild]
            constructor
            · rw [List.range_succ, List.map_append, ih.1]
              simp [hq]
            · trivial
          · have hfour : (digits consumed).1 = 4 := by
              have hle := hdigits consumed
              omega
            have hq : digits consumed = q4 := by
              apply Subtype.ext
              change (digits consumed).1 = q4.1
              rw [q4_val]
              exact hfour
            simp only [guidedPosition, hp, guidedStep, hdigit]
            simp only [if_false, HallNode.rightChild]
            constructor
            · rw [List.range_succ, List.map_append, ih.1]
              simp [hq]
            · trivial

theorem value_mem_guidedPosition_interval (digits : ℕ → PartialQuotient)
    (hdigits : ∀ n, (digits n).1 ≤ 4) (n : ℕ) :
    value 0 digits ∈ (guidedPosition digits n).node.interval := by
  have hinv := guidedPosition_invariant digits hdigits n
  rcases hp : guidedPosition digits n with ⟨⟨w, state⟩, consumed⟩
  rw [hp] at hinv
  simp only at hinv
  have hlen : consumed = w.length := by
    have h := congrArg List.length hinv.1
    simpa using h
  subst consumed
  cases state with
  | one =>
      exact value_mem_T1_of_prefix digits hdigits w hinv.1
  | two =>
      exact value_mem_T2_of_prefix digits hdigits w hinv.1 hinv.2
  | three =>
      exact value_mem_T3_of_prefix digits hdigits w hinv.1 hinv.2

theorem C4_subset_cantorStage (n : ℕ) : C 4 ⊆ cantorStage n := by
  rintro x ⟨digits, hdigits, rfl⟩
  change value 0 digits ∈ ⋃ v ∈ nodesAtLevel n, v.interval
  simp only [Set.mem_iUnion]
  exact ⟨(guidedPosition digits n).node,
    guidedPosition_mem_nodesAtLevel digits n,
    value_mem_guidedPosition_interval digits hdigits n⟩

def HallState.defaultDigit : HallState → PartialQuotient
  | .one => q1
  | .two => q2
  | .three => q3

/-- Extend the word of a node by a constant allowed tail appropriate to its
current state. -/
def HallNode.extendedDigits (v : HallNode) (n : ℕ) : PartialQuotient :=
  v.word.getD n v.state.defaultDigit

theorem map_range_extendedDigits (v : HallNode) :
    (List.range v.word.length).map v.extendedDigits = v.word := by
  apply List.ext_get
  · simp
  · intro i hi₁ hi₂
    simp [HallNode.extendedDigits, List.getD, hi₂]

theorem HallNode.extendedDigits_le_four (v : HallNode)
    (hw : ∀ a ∈ v.word, a.1 ≤ 4) (n : ℕ) :
    (v.extendedDigits n).1 ≤ 4 := by
  by_cases hn : n < v.word.length
  · have hmem : v.word[n] ∈ v.word := List.getElem_mem hn
    simpa [HallNode.extendedDigits, List.getD, hn] using hw v.word[n] hmem
  · rcases v with ⟨w, state⟩
    cases state <;> simp [HallNode.extendedDigits, HallState.defaultDigit,
      List.getD, hn, q1_val, q2_val, q3_val]

theorem HallNode.extendedValue_mem_interval (v : HallNode)
    (hw : ∀ a ∈ v.word, a.1 ≤ 4) :
    value 0 v.extendedDigits ∈ v.interval := by
  have hprefix := map_range_extendedDigits v
  have hbound := v.extendedDigits_le_four hw
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      exact value_mem_T1_of_prefix _ hbound w hprefix
  | two =>
      apply value_mem_T2_of_prefix _ hbound w hprefix
      simp [HallNode.extendedDigits, HallState.defaultDigit, List.getD,
        q2_val]
  | three =>
      apply value_mem_T3_of_prefix _ hbound w hprefix
      simp [HallNode.extendedDigits, HallState.defaultDigit, List.getD,
        q3_val]

theorem prefixMap_append_xi_mem_T1 (w : Word) (q : PartialQuotient)
    (hq : q.1 ≤ 4) :
    prefixMap (w ++ [q]) xi ∈ T1 w := by
  have htail :
      tailMap [q] delta ∈ Set.Icc delta epsilon := by
    apply tailMap_mem_delta_epsilon
    · intro a ha
      simp at ha
      simpa [ha] using hq
    · exact ⟨le_rfl, delta_le_epsilon⟩
  have hmem :=
    tailMap_mem_uIcc (w := w) delta_pos.le delta_le_epsilon epsilon_le_one htail
  simpa only [T1, prefixMap_eq_tailMap, one_div_eta, one_div_xi,
    tailMap_append, Set.uIcc_comm] using hmem

theorem HallNode.interval_subset_T1 (v : HallNode) :
    v.interval ⊆ T1 v.word := by
  rcases v with ⟨w, state⟩
  cases state with
  | one => exact fun _ h ↦ h
  | two =>
      apply Set.uIcc_subset_uIcc
      · exact Set.right_mem_uIcc
      · exact prefixMap_append_xi_mem_T1 w q2 (by rw [q2_val]; norm_num)
  | three =>
      apply Set.uIcc_subset_uIcc
      · exact Set.right_mem_uIcc
      · exact prefixMap_append_xi_mem_T1 w q3 (by rw [q3_val]; norm_num)

theorem HallNode.dist_le_cylinder {v : HallNode} {x y : ℝ}
    (hx : x ∈ v.interval) (hy : y ∈ v.interval) :
    dist x y ≤ 1 / 4 ^ (v.word.length / 2) := by
  have hx' := v.interval_subset_T1 hx
  have hy' := v.interval_subset_T1 hy
  unfold T1 at hx' hy'
  have hdist := Real.dist_le_of_mem_uIcc hx' hy'
  rw [prefixMap_eq_tailMap, prefixMap_eq_tailMap, one_div_eta, one_div_xi,
    Real.dist_eq] at hdist
  exact hdist.trans (abs_tailMap_le_cylinder v.word
    ⟨epsilon_pos.le, epsilon_le_one⟩
    ⟨delta_pos.le, delta_le_epsilon.trans epsilon_le_one⟩)

def HallState.offset : HallState → ℕ
  | .one => 0
  | .two => 1
  | .three => 2

def HallNode.rank (v : HallNode) : ℕ :=
  3 * v.word.length + v.state.offset

def HallNode.WordAllowed (v : HallNode) : Prop :=
  ∀ a ∈ v.word, a.1 ≤ 4

theorem HallNode.child_allowed_rank (v child : HallNode)
    (hchild : child ∈ v.children) (hv : v.WordAllowed) :
    child.WordAllowed ∧ v.rank + 1 ≤ child.rank := by
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      simp only [HallNode.children, HallNode.leftChild, HallNode.rightChild,
        List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl
      · constructor
        · intro a ha
          simp only [HallNode.WordAllowed] at hv ⊢
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact hv a ha
          · simp only [List.mem_singleton] at ha
            subst a
            rw [q1_val]
            norm_num
        · simp [HallNode.rank, HallState.offset]
      · exact ⟨hv, by simp [HallNode.rank, HallState.offset]⟩
  | two =>
      simp only [HallNode.children, HallNode.leftChild, HallNode.rightChild,
        List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl
      · constructor
        · intro a ha
          simp only [HallNode.WordAllowed] at hv ⊢
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact hv a ha
          · simp only [List.mem_singleton] at ha
            subst a
            rw [q2_val]
            norm_num
        · (simp [HallNode.rank, HallState.offset]; omega)
      · exact ⟨hv, by simp [HallNode.rank, HallState.offset]⟩
  | three =>
      simp only [HallNode.children, HallNode.leftChild, HallNode.rightChild,
        List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl
      · constructor
        · intro a ha
          simp only [HallNode.WordAllowed] at hv ⊢
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact hv a ha
          · simp only [List.mem_singleton] at ha
            subst a
            rw [q3_val]
            norm_num
        · (simp [HallNode.rank, HallState.offset]; omega)
      · constructor
        · intro a ha
          simp only [HallNode.WordAllowed] at hv ⊢
          rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact hv a ha
          · simp only [List.mem_singleton] at ha
            subst a
            rw [q4_val]
        · (simp [HallNode.rank, HallState.offset]; omega)

theorem nodeAtLevel_allowed_rank {n : ℕ} {v : HallNode}
    (hv : v ∈ nodesAtLevel n) :
    v.WordAllowed ∧ n ≤ v.rank := by
  induction n generalizing v with
  | zero =>
      simp only [nodesAtLevel_zero, List.mem_singleton] at hv
      subst v
      constructor
      · simp [HallNode.WordAllowed, rootNode]
      · simp [HallNode.rank, HallState.offset, rootNode]
  | succ n ih =>
      simp only [nodesAtLevel_succ, List.mem_flatMap] at hv
      rcases hv with ⟨parent, hp, hchild⟩
      have hparent := ih hp
      have hc := parent.child_allowed_rank v hchild hparent.1
      exact ⟨hc.1, le_trans (Nat.succ_le_succ hparent.2) hc.2⟩

/-- The recursive interval construction has exactly `C(4)` as its survivor. -/
theorem C4_eq_iInter_cantorStage :
    C 4 = ⋂ n, cantorStage n := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iInter]
    exact fun n ↦ C4_subset_cantorStage n hx
  · intro x hx
    have hxstage : ∀ n, x ∈ cantorStage n := Set.mem_iInter.mp hx
    have hex : ∀ k : ℕ, ∃ v : HallNode,
        v ∈ nodesAtLevel (6 * k + 2) ∧ x ∈ v.interval := by
      intro k
      have hxk := hxstage (6 * k + 2)
      change x ∈ ⋃ v ∈ nodesAtLevel (6 * k + 2), v.interval at hxk
      simp only [Set.mem_iUnion] at hxk
      rcases hxk with ⟨v, hv, hxv⟩
      exact ⟨v, hv, hxv⟩
    choose v hvlevel hxv using hex
    let y : ℕ → ℝ := fun k ↦ value 0 (v k).extendedDigits
    have hnode : ∀ k, (v k).WordAllowed ∧
        6 * k + 2 ≤ (v k).rank :=
      fun k ↦ nodeAtLevel_allowed_rank (hvlevel k)
    have hyC : ∀ k, y k ∈ C 4 := by
      intro k
      refine ⟨(v k).extendedDigits, (v k).extendedDigits_le_four (hnode k).1, rfl⟩
    have hydist : ∀ k, dist (y k) x ≤ (1 / 4 : ℝ) ^ k := by
      intro k
      have hyint := (v k).extendedValue_mem_interval (hnode k).1
      have hcyl := HallNode.dist_le_cylinder hyint (hxv k)
      have hklen : k ≤ (v k).word.length / 2 := by
        have hrank := (hnode k).2
        unfold HallNode.rank at hrank
        rcases hs : (v k).state with (_ | _ | _) <;> rw [hs] at hrank <;>
          simp only [HallState.offset] at hrank <;> omega
      have hpow :
          (1 / 4 : ℝ) ^ ((v k).word.length / 2) ≤ (1 / 4 : ℝ) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hklen
      have hpow' :
          1 / (4 : ℝ) ^ ((v k).word.length / 2) ≤ 1 / (4 : ℝ) ^ k := by
        simpa only [one_div_pow] using hpow
      simpa only [one_div_pow] using hcyl.trans hpow'
    have hytend : Filter.Tendsto y Filter.atTop (𝓝 x) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hpow : Filter.Tendsto (fun k : ℕ ↦ ((1 / 4 : ℝ) ^ k))
          Filter.atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hev : ∀ᶠ k : ℕ in Filter.atTop, (1 / 4 : ℝ) ^ k < ε :=
        hpow.eventually (Iio_mem_nhds hε)
      rcases Filter.eventually_atTop.1 hev with ⟨K, hK⟩
      refine ⟨K, fun k hk ↦ ?_⟩
      exact lt_of_le_of_lt (hydist k) (hK k hk)
    exact isClosed_C4.mem_of_tendsto hytend
      (Filter.Eventually.of_forall hyC)

theorem prefixMap_append_eta (w : Word) (q : PartialQuotient) :
    prefixMap (w ++ [q]) eta = prefixMap w ((q.1 : ℝ) + epsilon) := by
  rw [prefixMap_append_singleton, one_div_eta]

theorem prefixMap_append_xi (w : Word) (q : PartialQuotient) :
    prefixMap (w ++ [q]) xi = prefixMap w ((q.1 : ℝ) + delta) := by
  rw [prefixMap_append_singleton, one_div_xi]

theorem uIcc_diff_uIoo_eq_union_uIcc {a0 a1 a2 a3 : ℝ}
    (h01 : a0 ≤ a1) (h12 : a1 ≤ a2) (h23 : a2 ≤ a3) :
    Set.uIcc a0 a3 \ Set.uIoo a1 a2 =
      Set.uIcc a0 a1 ∪ Set.uIcc a2 a3 := by
  rw [Set.uIcc_of_le (h01.trans <| h12.trans h23),
    Set.uIoo_of_le h12, Set.uIcc_of_le h01, Set.uIcc_of_le h23]
  ext x
  constructor
  · rintro ⟨⟨h0x, hx3⟩, hxgap⟩
    by_cases hx1 : x ≤ a1
    · exact Or.inl ⟨h0x, hx1⟩
    · exact Or.inr ⟨by
        by_contra hxa2
        exact hxgap ⟨lt_of_not_ge hx1, lt_of_not_ge hxa2⟩, hx3⟩
  · rintro (hx | hx)
    · exact ⟨⟨hx.1, hx.2.trans (h12.trans h23)⟩,
        fun hgap ↦ (not_lt_of_ge hx.2) hgap.1⟩
    · exact ⟨⟨(h01.trans h12).trans hx.1, hx.2⟩,
        fun hgap ↦ (not_lt_of_ge hx.1) hgap.2⟩

theorem uIcc_diff_uIoo_of_monotone_or_antitone
    (f : ℝ → ℝ) {x0 x1 x2 x3 : ℝ}
    (_h01 : x0 ≤ x1) (_h12 : x1 ≤ x2) (_h23 : x2 ≤ x3)
    (hmono :
      (f x0 ≤ f x1 ∧ f x1 ≤ f x2 ∧ f x2 ≤ f x3) ∨
      (f x3 ≤ f x2 ∧ f x2 ≤ f x1 ∧ f x1 ≤ f x0)) :
    Set.uIcc (f x0) (f x3) \ Set.uIoo (f x1) (f x2) =
      Set.uIcc (f x0) (f x1) ∪ Set.uIcc (f x2) (f x3) := by
  rcases hmono with hmono | hanti
  · exact uIcc_diff_uIoo_eq_union_uIcc hmono.1 hmono.2.1 hmono.2.2
  · rw [Set.uIcc_comm (f x0), Set.uIoo_comm (f x1),
      Set.uIcc_comm (f x0), Set.uIcc_comm (f x2)]
    simpa [Set.union_comm] using
      (uIcc_diff_uIoo_eq_union_uIcc hanti.1 hanti.2.1 hanti.2.2)

theorem prefixMap_four_order (w : Word) (k : ℕ)
    (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    let x0 := (k : ℝ) + delta
    let x1 := (k : ℝ) + epsilon
    let x2 := (k : ℝ) + 1 + delta
    let x3 := 4 + epsilon
    (prefixMap w x0 ≤ prefixMap w x1 ∧
      prefixMap w x1 ≤ prefixMap w x2 ∧
      prefixMap w x2 ≤ prefixMap w x3) ∨
    (prefixMap w x3 ≤ prefixMap w x2 ∧
      prefixMap w x2 ≤ prefixMap w x1 ∧
      prefixMap w x1 ≤ prefixMap w x0) := by
  dsimp
  let x0 : ℝ := (k : ℝ) + delta
  let x1 : ℝ := (k : ℝ) + epsilon
  let x2 : ℝ := (k : ℝ) + 1 + delta
  let x3 : ℝ := 4 + epsilon
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hx0 : 0 < x0 := by
    dsimp [x0]
    linarith [delta_pos]
  have h01 : x0 ≤ x1 := by
    dsimp [x0, x1, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h12 : x1 ≤ x2 := by
    dsimp [x1, x2, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h23 : x2 ≤ x3 := by
    dsimp [x2, x3, delta, epsilon]
    interval_cases k <;> nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h01lt : x0 < x1 := by
    dsimp [x0, x1, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h12lt : x1 < x2 := by
    dsimp [x1, x2, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h23lt : x2 < x3 := by
    dsimp [x2, x3, delta, epsilon]
    interval_cases k <;> nlinarith [sqrt_two_sq, sqrt_two_pos]
  have hsub : Set.Icc x0 x3 ⊆ Set.Ioi (0 : ℝ) :=
    fun _ hx ↦ hx0.trans_le hx.1
  have hma :=
    ((continuousOn_prefixMap_pos w).mono hsub).strictMonoOn_of_injOn_Icc'
      (h01.trans <| h12.trans h23) ((injOn_prefixMap_pos w).mono hsub)
  have hx0mem : x0 ∈ Set.Icc x0 x3 :=
    ⟨le_rfl, h01.trans <| h12.trans h23⟩
  have hx1mem : x1 ∈ Set.Icc x0 x3 := ⟨h01, h12.trans h23⟩
  have hx2mem : x2 ∈ Set.Icc x0 x3 := ⟨h01.trans h12, h23⟩
  have hx3mem : x3 ∈ Set.Icc x0 x3 :=
    ⟨h01.trans <| h12.trans h23, le_rfl⟩
  rcases hma with hm | ha
  · exact Or.inl ⟨(hm hx0mem hx1mem h01lt).le,
      (hm hx1mem hx2mem h12lt).le, (hm hx2mem hx3mem h23lt).le⟩
  · exact Or.inr ⟨(ha hx2mem hx3mem h23lt).le,
      (ha hx1mem hx2mem h12lt).le, (ha hx0mem hx1mem h01lt).le⟩

theorem prefixMap_interval_split (w : Word) (k : ℕ)
    (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    let x0 := (k : ℝ) + delta
    let x1 := (k : ℝ) + epsilon
    let x2 := (k : ℝ) + 1 + delta
    let x3 := 4 + epsilon
    Set.uIcc (prefixMap w x0) (prefixMap w x3) \
        Set.uIoo (prefixMap w x1) (prefixMap w x2) =
      Set.uIcc (prefixMap w x0) (prefixMap w x1) ∪
        Set.uIcc (prefixMap w x2) (prefixMap w x3) := by
  dsimp
  let x0 : ℝ := (k : ℝ) + delta
  let x1 : ℝ := (k : ℝ) + epsilon
  let x2 : ℝ := (k : ℝ) + 1 + delta
  let x3 : ℝ := 4 + epsilon
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hx0 : 0 < x0 := by dsimp [x0]; linarith [delta_pos]
  have h01 : x0 ≤ x1 := by
    dsimp [x0, x1, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h12 : x1 ≤ x2 := by
    dsimp [x1, x2, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h23 : x2 ≤ x3 := by
    dsimp [x2, x3, delta, epsilon]
    interval_cases k <;> nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h01lt : x0 < x1 := by
    dsimp [x0, x1, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h12lt : x1 < x2 := by
    dsimp [x1, x2, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h23lt : x2 < x3 := by
    dsimp [x2, x3, delta, epsilon]
    interval_cases k <;> nlinarith [sqrt_two_sq, sqrt_two_pos]
  have hx3 : 0 < x3 := lt_of_lt_of_le hx0 (h01.trans <| h12.trans h23)
  have hsub : Set.Icc x0 x3 ⊆ Set.Ioi (0 : ℝ) := fun _ hx ↦ hx0.trans_le hx.1
  have hcont := (continuousOn_prefixMap_pos w).mono hsub
  have hinj := (injOn_prefixMap_pos w).mono hsub
  have hma :=
    hcont.strictMonoOn_of_injOn_Icc' (h01.trans <| h12.trans h23) hinj
  apply uIcc_diff_uIoo_of_monotone_or_antitone (prefixMap w) h01 h12 h23
  have hx0mem : x0 ∈ Set.Icc x0 x3 :=
    ⟨le_rfl, h01.trans <| h12.trans h23⟩
  have hx1mem : x1 ∈ Set.Icc x0 x3 := ⟨h01, h12.trans h23⟩
  have hx2mem : x2 ∈ Set.Icc x0 x3 := ⟨h01.trans h12, h23⟩
  have hx3mem : x3 ∈ Set.Icc x0 x3 :=
    ⟨h01.trans <| h12.trans h23, le_rfl⟩
  rcases hma with hm | ha
  · exact Or.inl ⟨(hm hx0mem hx1mem h01lt).le,
      (hm hx1mem hx2mem h12lt).le, (hm hx2mem hx3mem h23lt).le⟩
  · exact Or.inr ⟨(ha hx2mem hx3mem h23lt).le,
      (ha hx1mem hx2mem h12lt).le, (ha hx0mem hx1mem h01lt).le⟩

theorem HallNode.interval_diff_gap (v : HallNode) :
    v.interval \ v.gap =
      v.leftChild.interval ∪ v.rightChild.interval := by
  rcases v with ⟨w, state⟩
  cases state with
  | one =>
      have h := prefixMap_interval_split w 1 (by omega) (by omega)
      simp only [HallNode.interval, HallNode.gap, HallNode.leftChild,
        HallNode.rightChild, T1, T2, G1] at h ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      rw [eta_eq_one_add_delta, xi_eq_four_add_epsilon]
      simp only [q1_val, q2_val] at ⊢
      norm_num at h ⊢
      simpa [Set.uIcc_comm, add_assoc, add_comm, add_left_comm] using h
  | two =>
      have h := prefixMap_interval_split w 2 (by omega) (by omega)
      simp only [HallNode.interval, HallNode.gap, HallNode.leftChild,
        HallNode.rightChild, T1, T2, T3, G2] at h ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      rw [xi_eq_four_add_epsilon]
      simp only [q2_val, q3_val] at ⊢
      norm_num at h ⊢
      simpa [Set.uIcc_comm, add_assoc, add_comm, add_left_comm] using h
  | three =>
      have h := prefixMap_interval_split w 3 (by omega) (by omega)
      simp only [HallNode.interval, HallNode.gap, HallNode.leftChild,
        HallNode.rightChild, T1, T3, G3] at h ⊢
      simp_rw [prefixMap_append_eta, prefixMap_append_xi]
      rw [xi_eq_four_add_epsilon]
      simp only [q3_val, q4_val] at ⊢
      norm_num at h ⊢
      simpa [Set.uIcc_comm, add_assoc, add_comm, add_left_comm] using h

/-- One simultaneous subdivision removes exactly the gaps belonging to the
nodes at the preceding level. -/
theorem cantorStage_succ (n : ℕ) :
    cantorStage (n + 1) =
      ⋃ v ∈ nodesAtLevel n, (v.interval \ v.gap) := by
  classical
  ext x
  simp only [cantorStage, nodesAtLevel_succ, List.mem_flatMap,
    Set.mem_iUnion, HallNode.interval_diff_gap, Set.mem_union]
  constructor
  · rintro ⟨child, ⟨parent, hp, hc⟩, hx⟩
    refine ⟨parent, hp, ?_⟩
    simp only [HallNode.children, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro ⟨parent, hp, hx | hx⟩
    · exact ⟨parent.leftChild, ⟨parent, hp, by simp [HallNode.children]⟩, hx⟩
    · exact ⟨parent.rightChild, ⟨parent, hp, by simp [HallNode.children]⟩, hx⟩

/-- The finite stages form a decreasing sequence. -/
theorem cantorStage_succ_subset (n : ℕ) :
    cantorStage (n + 1) ⊆ cantorStage n := by
  rw [cantorStage_succ]
  rintro x hx
  simp only [Set.mem_iUnion] at hx
  rcases hx with ⟨v, hv, hx⟩
  change x ∈ ⋃ v ∈ nodesAtLevel n, v.interval
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, hx.1⟩

theorem antitone_cantorStage : Antitone cantorStage := by
  exact antitone_nat_of_succ_le cantorStage_succ_subset

/-- Every finite stage is compact. -/
theorem isCompact_cantorStage (n : ℕ) : IsCompact (cantorStage n) := by
  classical
  let nodes := nodesAtLevel n
  change IsCompact (⋃ v ∈ nodes, v.interval)
  induction nodes with
  | nil => simp
  | cons v nodes ih =>
      rw [show (⋃ u ∈ v :: nodes, u.interval) =
          v.interval ∪ ⋃ u ∈ nodes, u.interval by ext; simp]
      apply IsCompact.union
      · rcases v with ⟨w, state⟩
        cases state <;> exact isCompact_uIcc
      · exact ih

/-- A distinguished node witnessing that no finite stage is empty. -/
def leftSpine : ℕ → HallNode
  | 0 => rootNode
  | n + 1 => (leftSpine n).leftChild

theorem leftSpine_mem_nodesAtLevel (n : ℕ) :
    leftSpine n ∈ nodesAtLevel n := by
  induction n with
  | zero => simp [leftSpine]
  | succ n ih =>
      simp only [leftSpine, nodesAtLevel_succ, List.mem_flatMap]
      exact ⟨leftSpine n, ih, by simp [HallNode.children]⟩

theorem cantorStage_nonempty (n : ℕ) : (cantorStage n).Nonempty := by
  have hv := leftSpine_mem_nodesAtLevel n
  refine ⟨?_, ?_⟩
  · rcases leftSpine n with ⟨w, state⟩
    cases state with
    | one => exact prefixMap w eta
    | two => exact prefixMap w xi
    | three => exact prefixMap w xi
  · change _ ∈ ⋃ v ∈ nodesAtLevel n, v.interval
    simp only [Set.mem_iUnion]
    refine ⟨leftSpine n, hv, ?_⟩
    rcases leftSpine n with ⟨w, state⟩
    cases state <;> simp [HallNode.interval, T1, T2, T3, Set.left_mem_uIcc]

/-- The initial interval in Hall's construction has the endpoints stated in
Lemma 3.1 of `doc/main.tex`. -/
theorem T1_nil : T1 [] = Set.Icc delta epsilon := by
  rw [T1, prefixMap_nil, prefixMap_nil, one_div_eta, one_div_xi,
    Set.uIcc_of_ge delta_le_epsilon]

/--
Hall's length condition in complete-quotient coordinates.  For each of the
three state types, both intervals left after removing the gap are at least
as long as the gap itself.
-/
theorem hall_length_condition (w : Word) (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    let x0 := (k : ℝ) + delta
    let x1 := (k : ℝ) + epsilon
    let x2 := (k : ℝ) + 1 + delta
    let x3 := 4 + epsilon
    |prefixMap w x1 - prefixMap w x0| ≥
        |prefixMap w x2 - prefixMap w x1| ∧
      |prefixMap w x3 - prefixMap w x2| ≥
        |prefixMap w x2 - prefixMap w x1| := by
  dsimp
  let x0 : ℝ := (k : ℝ) + delta
  let x1 : ℝ := (k : ℝ) + epsilon
  let x2 : ℝ := (k : ℝ) + 1 + delta
  let x3 : ℝ := 4 + epsilon
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hx0 : 0 < x0 := by dsimp [x0]; linarith [delta_pos]
  have hx1 : 0 < x1 := by dsimp [x1]; linarith [epsilon_pos]
  have hx2 : 0 < x2 := by dsimp [x2]; linarith [delta_pos]
  have hx3 : 0 < x3 := by dsimp [x3]; linarith [epsilon_pos]
  have hs75 : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have hs43 : (4 / 3 : ℝ) < Real.sqrt 2 := by
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have hs32 : Real.sqrt 2 < (3 / 2 : ℝ) := by
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h01 : x0 ≤ x1 := by
    dsimp [x0, x1, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h12 : x1 ≤ x2 := by
    dsimp [x1, x2, delta, epsilon]
    nlinarith [sqrt_two_sq, sqrt_two_pos]
  have h23 : x2 ≤ x3 := by
    dsimp [x2, x3, delta, epsilon]
    interval_cases k <;> nlinarith [sqrt_two_sq, sqrt_two_pos]
  let Cq : ℝ := (mobiusCoeffs w).C
  let Dq : ℝ := (mobiusCoeffs w).D
  have hCq : 0 < Cq := by
    dsimp [Cq]
    exact_mod_cast mobius_C_pos w
  have hDq : 0 ≤ Dq := by positivity
  have hDC : Dq ≤ Cq := by
    dsimp [Dq, Cq]
    exact_mod_cast mobius_D_le_C w
  have hd0 : 0 < Cq * x0 + Dq := by positivity
  have hd1 : 0 < Cq * x1 + Dq := by positivity
  have hd2 : 0 < Cq * x2 + Dq := by positivity
  have hd3 : 0 < Cq * x3 + Dq := by positivity
  rw [abs_prefixMap_sub_prefixMap w hx1 hx0,
    abs_prefixMap_sub_prefixMap w hx2 hx1,
    abs_prefixMap_sub_prefixMap w hx3 hx2]
  change
    |x1 - x0| / ((Cq * x1 + Dq) * (Cq * x0 + Dq)) ≥
        |x2 - x1| / ((Cq * x2 + Dq) * (Cq * x1 + Dq)) ∧
      |x3 - x2| / ((Cq * x3 + Dq) * (Cq * x2 + Dq)) ≥
        |x2 - x1| / ((Cq * x2 + Dq) * (Cq * x1 + Dq))
  rw [abs_of_nonneg (sub_nonneg.2 h01), abs_of_nonneg (sub_nonneg.2 h12),
    abs_of_nonneg (sub_nonneg.2 h23)]
  constructor
  · apply (div_le_div_iff₀ (mul_pos hd2 hd1) (mul_pos hd1 hd0)).2
    have hcore :
        (x2 - x1) * (Cq * x0 + Dq) ≤
          (x1 - x0) * (Cq * x2 + Dq) := by
      dsimp [x0, x1, x2, delta, epsilon]
      interval_cases k <;> norm_num at * <;>
        nlinarith [sqrt_two_sq, sqrt_two_pos, hs75]
    have hmul := mul_nonneg hd1.le (sub_nonneg.2 hcore)
    nlinarith [hmul]
  · apply (div_le_div_iff₀ (mul_pos hd2 hd1) (mul_pos hd3 hd2)).2
    have hcore :
        (x2 - x1) * (Cq * x3 + Dq) ≤
          (x3 - x2) * (Cq * x1 + Dq) := by
      let coefC : ℝ :=
        (-2 * (k : ℝ) ^ 2 + 7 * k + 8 -
          ((k : ℝ) + 4) * Real.sqrt 2) / 2
      let coefD : ℝ := 3 * Real.sqrt 2 - k - 1
      have hcoefC : 0 ≤ coefC := by
        dsimp [coefC]
        interval_cases k <;> norm_num at * <;> nlinarith
      have hcoefD : 0 ≤ coefD := by
        dsimp [coefD]
        interval_cases k <;> norm_num at * <;> nlinarith
      have heq :
          (x3 - x2) * (Cq * x1 + Dq) -
              (x2 - x1) * (Cq * x3 + Dq) =
            Cq * coefC + Dq * coefD := by
        dsimp [x1, x2, x3, delta, epsilon, coefC, coefD]
        nlinarith [sqrt_two_sq]
      have hnonneg :
          0 ≤ Cq * coefC + Dq * coefD :=
        add_nonneg (mul_nonneg hCq.le hcoefC) (mul_nonneg hDq hcoefD)
      linarith
    have hmul := mul_nonneg hd2.le (sub_nonneg.2 hcore)
    nlinarith [hmul]

end Cantor
end HallRay
