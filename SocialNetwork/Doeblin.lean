/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Doeblin's criterion, the half that gives uniqueness

Theorem 1.2 of arXiv:2607.19651 gives the skeleton chain a unique invariant probability
measure, and gets it from a Doeblin minorisation.  [GL24] supplies that minorisation
explicitly for `M = 2`, and in a shape stronger than Doeblin's hypothesis in general: the
`2N`-step kernel is bounded below, uniformly in the starting matrix, by a multiple of the
Dirac mass at *one* state, the flat ladder.

That shape splits the theorem in two, and this file is the half that does not need
Markov-chain theory:

* **uniqueness** follows from the minorisation by an elementary argument, below;
* **existence** does not, and is not here.  [GL24] gets it from positive recurrence, and the
  classical construction of an invariant measure from one excursion is exactly the theory
  Mathlib does not have.

Nothing here mentions the social network, and nothing here is specific to the paper: it is a
statement about a Markov kernel on a countable space, written at that generality because it is
exactly as easy, and because `Kernel.Invariant` is all it consumes.

## The argument

Write `m x = min (μ {x}) (ν {x})` for two invariant probability measures and `T = ∑ₓ m x`, so
that `μ = ν` exactly when `T = 1`.  Invariance carries `m` forward: `m y ≥ ∑ₓ p x y · m x`,
since each of `μ {y}` and `ν {y}` is `∑ₓ p x y` against its own measure, and `m` is below
both.  Summing over `y` gives `T ≥ T`, which says nothing --- and the minorisation is what
turns it into something.  At the one state `l` where `p x l ≥ c` for every `x`,

```
μ {l} = ∑ₓ p x l · m x + ∑ₓ p x l · (μ {x} - m x)  ≥  ∑ₓ p x l · m x + c (1 - T),
```

and the same for `ν`, so the term at `l` carries a surplus of `c (1 - T)`.  Summing over `y`
now gives `T ≥ T + c (1 - T)`, whence `T = 1`.

**No counterpart in the paper**, which cites Doeblin's criterion rather than proving it.

## Main results

* `SocialNetwork.iterateKernel` — the `n`-step kernel, and its invariant measures.
* `SocialNetwork.eq_of_invariant_of_minorisation_on` — two invariant probability measures of a
  kernel minorised at a point, from every state of a set that carries them, coincide.
* `SocialNetwork.eq_of_invariant_of_iterate_minorisation` — the form Theorem 1.2 consumes, for
  a minorisation of the `n`-step kernel.
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace SocialNetwork

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-! ### Two sums in `ℝ≥0∞` -/

omit [Countable α] [MeasurableSingletonClass α] [MeasurableSpace α] in
/-- Truncated subtraction commutes with an infinite sum when the subtrahend is finite and
below the minuend.  `ENNReal.tsum_sub` says this for sums over `ℕ`; the index here is the
state space. -/
theorem tsum_tsub {ι : Type*} {f g : ι → ℝ≥0∞} (hg : ∑' i, g i ≠ ∞) (hfg : g ≤ f) :
    ∑' i, (f i - g i) = (∑' i, f i) - ∑' i, g i := by
  have h : (∑' i, (f i - g i)) + ∑' i, g i = ∑' i, f i := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun i => tsub_add_cancel_of_le (hfg i)
  rw [← h, ENNReal.add_sub_cancel_right hg]

/-- On a countable space with measurable singletons, a probability measure has total mass one
spread over the points. -/
theorem tsum_measure_singleton (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑' x : α, μ {x} = 1 := by
  have h := lintegral_countable' (μ := μ) (fun _ => (1 : ℝ≥0∞))
  simpa using h.symm

/-! ### Invariance, one point at a time -/

/-- One step of a kernel against a measure, one point at a time. -/
theorem bind_apply_singleton (κ : Kernel α α) (μ : Measure α) (y : α) :
    (μ.bind κ) {y} = ∑' x : α, κ x {y} * μ {x} := by
  rw [Measure.bind_apply (MeasurableSet.singleton y) (Kernel.aemeasurable _),
    lintegral_countable']

/-- The invariance equation in coordinates: `μ {y} = ∑ₓ p (x, y) μ {x}`. -/
theorem measure_singleton_of_invariant (κ : Kernel α α) {μ : Measure α}
    (hμ : Kernel.Invariant κ μ) (y : α) : μ {y} = ∑' x : α, κ x {y} * μ {x} := by
  conv_lhs => rw [← hμ.def]
  exact bind_apply_singleton κ μ y

/-! ### The `n`-step kernel -/

/-- The `n`-step kernel `κⁿ`.  Doeblin's hypothesis is a minorisation of one of these, not of
`κ` itself: for the skeleton chain it is the `2N`-step kernel that [GL24] bounds below. -/
noncomputable def iterateKernel (κ : Kernel α α) : ℕ → Kernel α α
  | 0 => Kernel.id
  | n + 1 => κ ∘ₖ iterateKernel κ n

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem iterateKernel_zero (κ : Kernel α α) : iterateKernel κ 0 = Kernel.id := rfl

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem iterateKernel_succ (κ : Kernel α α) (n : ℕ) :
    iterateKernel κ (n + 1) = κ ∘ₖ iterateKernel κ n := rfl

instance isMarkovKernel_iterateKernel (κ : Kernel α α) [IsMarkovKernel κ] :
    ∀ n, IsMarkovKernel (iterateKernel κ n)
  | 0 => by rw [iterateKernel]; infer_instance
  | n + 1 => by
      have := isMarkovKernel_iterateKernel κ n
      rw [iterateKernel]; infer_instance

omit [Countable α] [MeasurableSingletonClass α] in
/-- An invariant measure of `κ` is invariant for every `κⁿ`. -/
theorem invariant_iterateKernel (κ : Kernel α α) {μ : Measure α}
    (hμ : Kernel.Invariant κ μ) : ∀ n, Kernel.Invariant (iterateKernel κ n) μ
  | 0 => by
      rw [iterateKernel]
      exact Measure.id_comp
  | n + 1 => by
      rw [iterateKernel]
      exact hμ.comp (invariant_iterateKernel κ hμ n)

omit [Countable α] [MeasurableSingletonClass α] in
/-- The `n + 1`-step kernel, with the extra step taken **first** rather than last.  The two
recursions agree because composition of kernels is associative, and this one is the one that
matches a first-step decomposition on a path space. -/
theorem iterateKernel_succ' (κ : Kernel α α) [IsSFiniteKernel κ] : ∀ n : ℕ,
    iterateKernel κ (n + 1) = iterateKernel κ n ∘ₖ κ
  | 0 => by rw [iterateKernel_succ, iterateKernel_zero, Kernel.comp_id, Kernel.id_comp]
  | n + 1 => by
      conv_lhs => rw [iterateKernel_succ, iterateKernel_succ' κ n]
      rw [← Kernel.comp_assoc, ← iterateKernel_succ]

omit [Countable α] [MeasurableSingletonClass α] in
theorem iterateKernel_succ_apply' (κ : Kernel α α) [IsSFiniteKernel κ] (n : ℕ) (x : α)
    {A : Set α} (hA : MeasurableSet A) :
    iterateKernel κ (n + 1) x A = ∫⁻ y, iterateKernel κ n y A ∂(κ x) := by
  rw [iterateKernel_succ', Kernel.comp_apply' _ _ _ hA]

omit [Countable α] [MeasurableSingletonClass α] in
/-- `κ^{m+n} = κ^m ∘ κ^n`: the steps of an iterate can be split anywhere. -/
theorem iterateKernel_add (κ : Kernel α α) [IsSFiniteKernel κ] (m : ℕ) : ∀ n : ℕ,
    iterateKernel κ (m + n) = iterateKernel κ m ∘ₖ iterateKernel κ n
  | 0 => by rw [Nat.add_zero, iterateKernel_zero, Kernel.comp_id]
  | n + 1 => by
      rw [← Nat.add_assoc, iterateKernel_succ', iterateKernel_add κ m n, Kernel.comp_assoc,
        ← iterateKernel_succ']

/-! ### The criterion -/

/-- **Doeblin's criterion, the uniqueness half.**  If a Markov kernel on a countable space is
bounded below, uniformly in the starting point, by `c > 0` times the Dirac mass at a single
state `l`, then it has at most one invariant probability measure.

No irreducibility, no aperiodicity, no recurrence, and no existence theorem: the minorisation
at one point is doing all the work. -/
theorem eq_of_invariant_of_minorisation_on (κ : Kernel α α) [IsMarkovKernel κ] {S : Set α}
    {l : α} {c : ℝ≥0∞} (hc : 0 < c) (hmin : ∀ x ∈ S, c ≤ κ x {l}) {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμS : μ Sᶜ = 0) (hνS : ν Sᶜ = 0)
    (hμ : Kernel.Invariant κ μ) (hν : Kernel.Invariant κ ν) : μ = ν := by
  classical
  set m : α → ℝ≥0∞ := fun x => min (μ {x}) (ν {x}) with hm
  set T : ℝ≥0∞ := ∑' x : α, m x with hT
  -- `T ≤ 1`, so every subtraction below is a subtraction of finite quantities
  have hTle : T ≤ 1 := by
    rw [hT, ← tsum_measure_singleton (α := α) μ]
    exact ENNReal.tsum_le_tsum fun x => min_le_left _ _
  have hTne : T ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hTle
  -- the mass `m` carried forward one step
  set G : α → ℝ≥0∞ := fun y => ∑' x : α, κ x {y} * m x with hG
  have hGT : ∑' y : α, G y = T := by
    rw [hG, ENNReal.tsum_comm]
    refine tsum_congr fun x => ?_
    rw [ENNReal.tsum_mul_right, tsum_measure_singleton (κ x), one_mul]
  -- the surplus at `l`, which is where the minorisation enters
  have hmass : ∀ ρ : Measure α, IsProbabilityMeasure ρ → (∀ x, m x ≤ ρ {x}) →
      ρ Sᶜ = 0 → Kernel.Invariant κ ρ → G l + c * (1 - T) ≤ ρ {l} := by
    intro ρ hρ hmρ hρS hinv
    have hsplit : ρ {l} = G l + ∑' x : α, κ x {l} * (ρ {x} - m x) := by
      rw [measure_singleton_of_invariant κ hinv l, hG, ← ENNReal.tsum_add]
      refine tsum_congr fun x => ?_
      rw [← mul_add, add_tsub_cancel_of_le (hmρ x)]
    have hsurplus : c * (1 - T) ≤ ∑' x : α, κ x {l} * (ρ {x} - m x) := by
      have hsub : ∑' x : α, (ρ {x} - m x) = 1 - T := by
        rw [tsum_tsub hTne hmρ, tsum_measure_singleton ρ]
      rw [← hsub, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ S
      · gcongr
        exact hmin x hx
      · have hx0 : ρ {x} = 0 := measure_mono_null (Set.singleton_subset_iff.2 hx) hρS
        rw [hx0]
        simp
    rw [hsplit]
    exact add_le_add le_rfl hsurplus
  -- the same mass carried forward, without the surplus
  have hGle : ∀ y, G y ≤ m y := by
    intro y
    refine le_min ?_ ?_
    · rw [measure_singleton_of_invariant κ hμ y]
      exact ENNReal.tsum_le_tsum fun x => by gcongr; exact min_le_left _ _
    · rw [measure_singleton_of_invariant κ hν y]
      exact ENNReal.tsum_le_tsum fun x => by gcongr; exact min_le_right _ _
  have hml : G l + c * (1 - T) ≤ m l :=
    le_min (hmass μ ‹_› (fun x => min_le_left _ _) hμS hμ)
      (hmass ν ‹_› (fun x => min_le_right _ _) hνS hν)
  -- summing over `y` gives `T ≥ T + c (1 - T)`
  have hstep : T + c * (1 - T) ≤ T := by
    have hsplitG : ∑' y : α, G y = G l + ∑' y : α, (if y = l then 0 else G y) :=
      ENNReal.tsum_eq_add_tsum_ite l
    have hsplitm : ∑' y : α, m y = m l + ∑' y : α, (if y = l then 0 else m y) :=
      ENNReal.tsum_eq_add_tsum_ite l
    have htail : ∑' y : α, (if y = l then 0 else G y)
        ≤ ∑' y : α, (if y = l then 0 else m y) := by
      refine ENNReal.tsum_le_tsum fun y => ?_
      split
      · exact le_rfl
      · exact hGle y
    calc T + c * (1 - T)
        = (∑' y : α, G y) + c * (1 - T) := by rw [hGT]
      _ = (G l + c * (1 - T)) + ∑' y : α, (if y = l then 0 else G y) := by
          rw [hsplitG]; ring
      _ ≤ m l + ∑' y : α, (if y = l then 0 else m y) := add_le_add hml htail
      _ = ∑' y : α, m y := hsplitm.symm
      _ = T := hT.symm
  -- so the surplus vanishes, and `T = 1`
  have hzero : c * (1 - T) = 0 := by
    have h : T + c * (1 - T) ≤ T + 0 := by simpa using hstep
    simpa using (ENNReal.add_le_add_iff_left hTne).1 h
  have hone : (1 : ℝ≥0∞) ≤ T := by
    rcases (mul_eq_zero.1 hzero) with h | h
    · exact absurd h hc.ne'
    · exact tsub_eq_zero_iff_le.1 h
  -- and a probability measure that dominates its own minimum everywhere is that minimum
  have hTeq : T = 1 := le_antisymm hTle hone
  have hmeq : ∀ ρ : Measure α, IsProbabilityMeasure ρ → (∀ x, m x ≤ ρ {x}) →
      ∀ x, ρ {x} = m x := by
    intro ρ hρ hmρ x
    have hsub : ∑' y : α, (ρ {y} - m y) = 0 := by
      rw [tsum_tsub hTne hmρ, tsum_measure_singleton ρ, ← hT, hTeq, tsub_self]
    have := (ENNReal.tsum_eq_zero.1 hsub) x
    exact le_antisymm (tsub_eq_zero_iff_le.1 this) (hmρ x)
  refine Measure.ext_of_singleton fun x => ?_
  rw [hmeq μ ‹_› (fun x => min_le_left _ _) x, hmeq ν ‹_› (fun x => min_le_right _ _) x]

/-- The plain form, when the minorisation holds from every state. -/
theorem eq_of_invariant_of_minorisation (κ : Kernel α α) [IsMarkovKernel κ] {l : α}
    {c : ℝ≥0∞} (hc : 0 < c) (hmin : ∀ x, c ≤ κ x {l}) {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : Kernel.Invariant κ μ)
    (hν : Kernel.Invariant κ ν) : μ = ν :=
  eq_of_invariant_of_minorisation_on κ (S := Set.univ) hc (fun x _ => hmin x)
    (by simp) (by simp) hμ hν

/-- **The form Theorem 1.2 consumes.**  A minorisation of the `n`-step kernel at a single
state, valid from every state of an absorbing set that carries the measures, makes the
invariant probability measures of `κ` a subsingleton.

The set is there because the chain of the paper lives on the state space `S` of equation (2),
which is not all of `Pressure N M`: outside `S` there is no reason for the chain to reach a
ladder at all, and `μ^β` is required to be carried by `S`. -/
theorem eq_of_invariant_of_iterate_minorisation (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ)
    {S : Set α} {l : α} {c : ℝ≥0∞} (hc : 0 < c)
    (hmin : ∀ x ∈ S, c ≤ iterateKernel κ n x {l}) {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμS : μ Sᶜ = 0) (hνS : ν Sᶜ = 0)
    (hμ : Kernel.Invariant κ μ) (hν : Kernel.Invariant κ ν) : μ = ν :=
  eq_of_invariant_of_minorisation_on (iterateKernel κ n) hc hmin hμS hνS
    (invariant_iterateKernel κ hμ n) (invariant_iterateKernel κ hν n)

/-! ### The excursion measure

The other half of the criterion.  From the minorisation, the chain started at `l` returns to
`l` with a geometric tail, so the mass it spreads over one excursion is finite, and
normalising it gives an invariant probability measure.  The construction is the classical one;
what makes it elementary here is that the state space is countable, so everything is a sum in
`ℝ≥0∞` and no topology is needed.

Write `Q^m (y) = P_l (Ũ_m = y, Ũ_j ≠ l for 1 ≤ j ≤ m)` for the mass the excursion carries at
time `m` — `SocialNetwork.excursion` — and `ν = ∑_m Q^m`.  Three facts do it:

* `ν (l) = 1`, since only `m = 0` contributes there;
* `∑_y ν (y) = ∑_m P_l (R_l > m) < ∞`, because `P_l (R_l > m) ≤ (1 - c)^m`;
* `ν κ ≤ ν`, with equality off `l` by the recursion, and `≤` at `l` because the returns sum to
  at most one.

And `ν κ ≤ ν` with equal total mass is equality, the total mass being finite: the same step
that ends the uniqueness proof. -/

section Excursion

open scoped Classical in
/-- The probability of *not* landing on `l` in one step. -/
noncomputable def escape (κ : Kernel α α) (l : α) (x : α) : ℝ≥0∞ :=
  ∑' y : α, if y = l then 0 else κ x {y}

theorem hit_add_escape (κ : Kernel α α) [IsMarkovKernel κ] (l x : α) :
    κ x {l} + escape κ l x = 1 := by
  classical
  have h := ENNReal.tsum_eq_add_tsum_ite (f := fun y : α => κ x {y}) l
  rw [tsum_measure_singleton (κ x)] at h
  rw [escape]
  exact h.symm

open scoped Classical in
/-- The mass the excursion from `l` carries at time `m`:
`excursion κ l m y = P_l (Ũ_m = y, and Ũ_j ≠ l for every 1 ≤ j ≤ m)`. -/
noncomputable def excursion (κ : Kernel α α) (l : α) : ℕ → α → ℝ≥0∞
  | 0, y => if y = l then 1 else 0
  | m + 1, y => if y = l then 0 else ∑' x : α, excursion κ l m x * κ x {y}

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem excursion_zero_self (κ : Kernel α α) (l : α) : excursion κ l 0 l = 1 := by
  classical
  exact if_pos rfl

omit [Countable α] [MeasurableSingletonClass α] in
theorem excursion_zero_of_ne (κ : Kernel α α) {l y : α} (h : y ≠ l) :
    excursion κ l 0 y = 0 := by
  classical
  exact if_neg h

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem excursion_succ_self (κ : Kernel α α) (l : α) (m : ℕ) :
    excursion κ l (m + 1) l = 0 := by
  classical
  exact if_pos rfl

omit [Countable α] [MeasurableSingletonClass α] in
theorem excursion_succ_of_ne (κ : Kernel α α) {l y : α} (h : y ≠ l) (m : ℕ) :
    excursion κ l (m + 1) y = ∑' x : α, excursion κ l m x * κ x {y} := by
  classical
  exact if_neg h

/-- `P_l (R_l > m)`: the excursion has not come back to `l` by time `m`. -/
noncomputable def excursionMass (κ : Kernel α α) (l : α) (m : ℕ) : ℝ≥0∞ :=
  ∑' y : α, excursion κ l m y

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem excursionMass_zero (κ : Kernel α α) (l : α) : excursionMass κ l 0 = 1 := by
  rw [excursionMass, tsum_eq_single l fun y hy => excursion_zero_of_ne κ hy,
    excursion_zero_self]

omit [Countable α] [MeasurableSingletonClass α] in
open scoped Classical in
theorem escape_eq_tsum (κ : Kernel α α) (l x : α) :
    escape κ l x = ∑' y : α, (if y = l then 0 else κ x {y}) := rfl

omit [Countable α] [MeasurableSingletonClass α] in
theorem excursionMass_succ (κ : Kernel α α) (l : α) (m : ℕ) :
    excursionMass κ l (m + 1) = ∑' x : α, excursion κ l m x * escape κ l x := by
  classical
  have h : ∀ y : α, excursion κ l (m + 1) y
      = ∑' x : α, excursion κ l m x * (if y = l then 0 else κ x {y}) := by
    intro y
    by_cases hy : y = l
    · rw [hy, excursion_succ_self]
      simp
    · rw [excursion_succ_of_ne κ hy]
      simp [hy]
  rw [excursionMass, tsum_congr h, ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [escape_eq_tsum]
  exact ENNReal.tsum_mul_left

/-- The mass the excursion gives back to `l` between time `m` and time `m + 1`. -/
noncomputable def excursionReturn (κ : Kernel α α) (l : α) (m : ℕ) : ℝ≥0∞ :=
  ∑' x : α, excursion κ l m x * κ x {l}

/-- The excursion mass decomposes at every step: what it had is what returns plus what it
keeps. -/
theorem excursionMass_eq_add (κ : Kernel α α) [IsMarkovKernel κ] (l : α) (m : ℕ) :
    excursionMass κ l m = excursionReturn κ l m + excursionMass κ l (m + 1) := by
  rw [excursionMass_succ, excursionReturn, ← ENNReal.tsum_add, excursionMass]
  refine tsum_congr fun x => ?_
  rw [← mul_add, hit_add_escape κ l x, mul_one]

theorem sum_excursionReturn_add (κ : Kernel α α) [IsMarkovKernel κ] (l : α) :
    ∀ K : ℕ, (∑ m ∈ Finset.range K, excursionReturn κ l m) + excursionMass κ l K = 1
  | 0 => by simp
  | K + 1 => by
      rw [Finset.sum_range_succ, add_assoc, ← excursionMass_eq_add]
      exact sum_excursionReturn_add κ l K

/-- The returns sum to at most one: the chain cannot come back more than once. -/
theorem tsum_excursionReturn_le (κ : Kernel α α) [IsMarkovKernel κ] (l : α) :
    ∑' m : ℕ, excursionReturn κ l m ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun K => ?_
  calc ∑ m ∈ Finset.range K, excursionReturn κ l m
      ≤ (∑ m ∈ Finset.range K, excursionReturn κ l m) + excursionMass κ l K := le_self_add
    _ = 1 := sum_excursionReturn_add κ l K

/-! ### The geometric tail -/

variable {S : Set α} {l : α} {c : ℝ≥0∞}

omit [Countable α] [MeasurableSingletonClass α] in
/-- The excursion stays inside an absorbing set that contains its starting point. -/
theorem excursion_eq_zero_of_notMem (κ : Kernel α α) (hlS : l ∈ S)
    (habs : ∀ x ∈ S, κ x Sᶜ = 0) (m : ℕ) {y : α} (hy : y ∉ S) : excursion κ l m y = 0 := by
  induction m generalizing y with
  | zero => exact excursion_zero_of_ne κ fun h => hy (by rw [h]; exact hlS)
  | succ m ih =>
      rw [excursion_succ_of_ne κ (fun h => hy (by rw [h]; exact hlS))]
      refine ENNReal.tsum_eq_zero.2 fun x => ?_
      by_cases hx : x ∈ S
      · have hzero : κ x {y} = 0 :=
          measure_mono_null (Set.singleton_subset_iff.2 hy) (habs x hx)
        rw [hzero, mul_zero]
      · rw [ih hx, zero_mul]

/-- **The geometric tail.**  Each step costs the excursion a factor `1 - c`, because the
minorisation gives the chain probability at least `c` of returning to `l`. -/
theorem excursionMass_succ_le (κ : Kernel α α) [IsMarkovKernel κ] (hlS : l ∈ S)
    (habs : ∀ x ∈ S, κ x Sᶜ = 0) (hmin : ∀ x ∈ S, c ≤ κ x {l}) (m : ℕ) :
    excursionMass κ l (m + 1) ≤ (1 - c) * excursionMass κ l m := by
  rw [excursionMass_succ, excursionMass, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ S
  · have hle : escape κ l x + c ≤ 1 := by
      calc escape κ l x + c ≤ escape κ l x + κ x {l} := add_le_add le_rfl (hmin x hx)
        _ = 1 := by rw [add_comm]; exact hit_add_escape κ l x
    have hcne : c ≠ ∞ := by
      have : c ≤ 1 := le_trans (hmin x hx) prob_le_one
      exact ne_top_of_le_ne_top ENNReal.one_ne_top this
    have hesc : escape κ l x ≤ 1 - c :=
      calc escape κ l x = escape κ l x + c - c := (ENNReal.add_sub_cancel_right hcne).symm
        _ ≤ 1 - c := tsub_le_tsub_right hle c
    calc excursion κ l m x * escape κ l x ≤ excursion κ l m x * (1 - c) := by gcongr
      _ = (1 - c) * excursion κ l m x := mul_comm _ _
  · rw [excursion_eq_zero_of_notMem κ hlS habs m hx, zero_mul, mul_zero]

theorem excursionMass_le_pow (κ : Kernel α α) [IsMarkovKernel κ] (hlS : l ∈ S)
    (habs : ∀ x ∈ S, κ x Sᶜ = 0) (hmin : ∀ x ∈ S, c ≤ κ x {l}) :
    ∀ m : ℕ, excursionMass κ l m ≤ (1 - c) ^ m
  | 0 => by simp
  | m + 1 => by
      calc excursionMass κ l (m + 1) ≤ (1 - c) * excursionMass κ l m :=
            excursionMass_succ_le κ hlS habs hmin m
        _ ≤ (1 - c) * (1 - c) ^ m := by
            have h := excursionMass_le_pow κ hlS habs hmin m
            gcongr
        _ = (1 - c) ^ (m + 1) := by rw [pow_succ]; ring

end Excursion

/-! ### The excursion measure, and the invariant measure it normalises to -/

section ExcursionMeasure

/-- The excursion measure `ν (y) = ∑_m P_l (Ũ_m = y, R_l > m)`: the mass the chain spreads
over one excursion away from `l`. -/
noncomputable def excursionFun (κ : Kernel α α) (l : α) (y : α) : ℝ≥0∞ :=
  ∑' m : ℕ, excursion κ l m y

omit [Countable α] [MeasurableSingletonClass α] in
@[simp] theorem excursionFun_self (κ : Kernel α α) (l : α) : excursionFun κ l l = 1 := by
  rw [excursionFun, tsum_eq_zero_add' ENNReal.summable]
  simp

omit [Countable α] [MeasurableSingletonClass α] in
theorem tsum_excursionFun (κ : Kernel α α) (l : α) :
    ∑' y : α, excursionFun κ l y = ∑' m : ℕ, excursionMass κ l m := ENNReal.tsum_comm

omit [Countable α] [MeasurableSingletonClass α] in
theorem le_one_of_minorisation (κ : Kernel α α) [IsMarkovKernel κ] {S : Set α} {l : α}
    {c : ℝ≥0∞} (hlS : l ∈ S) (hmin : ∀ x ∈ S, c ≤ κ x {l}) : c ≤ 1 :=
  le_trans (hmin l hlS) prob_le_one

/-- The excursion carries finite mass: the returns have a geometric tail, so the excursion
does not last forever.  This is where the minorisation is spent. -/
theorem tsum_excursionFun_ne_top (κ : Kernel α α) [IsMarkovKernel κ] {S : Set α} {l : α}
    {c : ℝ≥0∞} (hc : 0 < c) (hlS : l ∈ S)
    (habs : ∀ x ∈ S, κ x Sᶜ = 0) (hmin : ∀ x ∈ S, c ≤ κ x {l}) :
    (∑' y : α, excursionFun κ l y) ≠ ∞ := by
  have hgeom : ∑' m : ℕ, excursionMass κ l m ≤ ∑' m : ℕ, (1 - c) ^ m :=
    ENNReal.tsum_le_tsum (excursionMass_le_pow κ hlS habs hmin)
  have hcle : c ≤ 1 := le_one_of_minorisation κ hlS hmin
  have hinv : ∑' m : ℕ, (1 - c) ^ m = c⁻¹ := by
    rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hcle]
  rw [tsum_excursionFun]
  exact ne_top_of_le_ne_top (by rw [hinv]; exact ENNReal.inv_ne_top.2 hc.ne') hgeom

omit [Countable α] [MeasurableSingletonClass α] in
/-- One step of the kernel against the excursion measure, layer by layer. -/
theorem tsum_excursionFun_mul_eq (κ : Kernel α α) (l y : α) :
    ∑' x : α, excursionFun κ l x * κ x {y}
      = ∑' m : ℕ, ∑' x : α, excursion κ l m x * κ x {y} := by
  rw [show (fun x : α => excursionFun κ l x * κ x {y})
      = fun x : α => ∑' m : ℕ, excursion κ l m x * κ x {y} from
    funext fun x => by rw [excursionFun, ENNReal.tsum_mul_right]]
  exact ENNReal.tsum_comm

omit [Countable α] [MeasurableSingletonClass α] in
/-- Off `l` the excursion measure reproduces itself exactly: the recursion *is* one step of
the kernel. -/
theorem tsum_excursionFun_mul_of_ne (κ : Kernel α α) {l y : α} (hy : y ≠ l) :
    ∑' x : α, excursionFun κ l x * κ x {y} = excursionFun κ l y := by
  have h0 : excursionFun κ l y = ∑' m : ℕ, excursion κ l (m + 1) y := by
    rw [excursionFun, tsum_eq_zero_add' ENNReal.summable, excursion_zero_of_ne κ hy, zero_add]
  rw [tsum_excursionFun_mul_eq, tsum_congr fun m => (excursion_succ_of_ne κ hy m).symm]
  exact h0.symm

variable {S : Set α} {l : α} {c : ℝ≥0∞}

/-- At `l` the excursion measure can only lose: what comes back is the total of the returns,
which is at most one. -/
theorem tsum_excursionFun_mul_le (κ : Kernel α α) [IsMarkovKernel κ] (l y : α) :
    ∑' x : α, excursionFun κ l x * κ x {y} ≤ excursionFun κ l y := by
  by_cases hy : y = l
  · subst hy
    rw [tsum_excursionFun_mul_eq, excursionFun_self]
    exact tsum_excursionReturn_le κ _
  · exact le_of_eq (tsum_excursionFun_mul_of_ne κ hy)

/-- **The excursion measure is invariant.**  It loses nothing at `l` either, because what it
would lose there it would have to lose from a finite total, and the total is preserved. -/
theorem tsum_excursionFun_mul (κ : Kernel α α) [IsMarkovKernel κ] (hc : 0 < c) (hlS : l ∈ S)
    (habs : ∀ x ∈ S, κ x Sᶜ = 0) (hmin : ∀ x ∈ S, c ≤ κ x {l}) (y : α) :
    ∑' x : α, excursionFun κ l x * κ x {y} = excursionFun κ l y := by
  have hle : (fun z : α => ∑' x : α, excursionFun κ l x * κ x {z}) ≤ excursionFun κ l :=
    fun z => tsum_excursionFun_mul_le κ l z
  have htotal : ∑' z : α, (∑' x : α, excursionFun κ l x * κ x {z})
      = ∑' z : α, excursionFun κ l z := by
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun x => by rw [ENNReal.tsum_mul_left, tsum_measure_singleton (κ x), mul_one]
  have hfin : (∑' z : α, ∑' x : α, excursionFun κ l x * κ x {z}) ≠ ∞ := by
    rw [htotal]
    exact tsum_excursionFun_ne_top κ hc hlS habs hmin
  have hsub : ∑' z : α, (excursionFun κ l z - ∑' x : α, excursionFun κ l x * κ x {z}) = 0 := by
    rw [tsum_tsub hfin hle, htotal, tsub_self]
  have hz := (ENNReal.tsum_eq_zero.1 hsub) y
  exact le_antisymm (hle y) (tsub_eq_zero_iff_le.1 hz)

/-- A weight function that is non-zero, of finite total mass, carried by `S` and reproduced by
one step of `κ` normalises to an invariant probability measure carried by `S`.  This is the
last step of both existence proofs below. -/
theorem exists_invariant_of_weight (κ : Kernel α α) (f : α → ℝ≥0∞)
    (hne : (∑' y : α, f y) ≠ 0) (htop : (∑' y : α, f y) ≠ ∞) (hS : ∀ y ∉ S, f y = 0)
    (hinv : ∀ y : α, ∑' x : α, f x * κ x {y} = f y) :
    ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ Sᶜ = 0 ∧ Kernel.Invariant κ μ := by
  classical
  set p : PMF α := PMF.normalize f hne htop with hp
  have hsing : ∀ x : α, p.toMeasure {x} = f x * (∑' z : α, f z)⁻¹ := fun x => by
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x), hp, PMF.normalize_apply]
  refine ⟨p.toMeasure, inferInstance, ?_, ?_⟩
  · rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete]
    refine ENNReal.tsum_eq_zero.2 fun x => ?_
    by_cases hx : x ∈ S
    · exact Set.indicator_of_notMem (by simpa using hx) _
    · rw [Set.indicator_of_mem hx, hp, PMF.normalize_apply, hS x hx, zero_mul]
  · show p.toMeasure.bind κ = p.toMeasure
    refine Measure.ext_of_singleton fun y => ?_
    rw [bind_apply_singleton]
    calc ∑' x : α, κ x {y} * p.toMeasure {x}
        = ∑' x : α, f x * κ x {y} * (∑' z : α, f z)⁻¹ :=
          tsum_congr fun x => by rw [hsing x]; ring
      _ = (∑' x : α, f x * κ x {y}) * (∑' z : α, f z)⁻¹ := ENNReal.tsum_mul_right
      _ = f y * (∑' z : α, f z)⁻¹ := by rw [hinv y]
      _ = p.toMeasure {y} := (hsing y).symm

/-- **Doeblin's criterion, the existence half.**  A Markov kernel on a countable space whose
one-step kernel is bounded below at a single state `l`, uniformly over an absorbing set `S`
containing `l`, has an invariant probability measure carried by `S`.

The measure is the excursion measure of `SocialNetwork.excursionFun`, normalised.  No
irreducibility, no aperiodicity, and no recurrence theory: the minorisation is what makes the
excursion end, and the rest is the last-exit decomposition, written in coordinates. -/
theorem exists_invariant_of_minorisation (κ : Kernel α α) [IsMarkovKernel κ] (hc : 0 < c)
    (hlS : l ∈ S) (habs : ∀ x ∈ S, κ x Sᶜ = 0) (hmin : ∀ x ∈ S, c ≤ κ x {l}) :
    ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ Sᶜ = 0 ∧ Kernel.Invariant κ μ := by
  refine exists_invariant_of_weight κ (excursionFun κ l) ?_
    (tsum_excursionFun_ne_top κ hc hlS habs hmin) ?_ (tsum_excursionFun_mul κ hc hlS habs hmin)
  · refine fun h => one_ne_zero (α := ℝ≥0∞) ?_
    rw [← excursionFun_self κ l]
    exact ENNReal.tsum_eq_zero.1 h l
  · exact fun y hy =>
      ENNReal.tsum_eq_zero.2 fun m => excursion_eq_zero_of_notMem κ hlS habs m hy

end ExcursionMeasure

/-! ### From an invariant measure of an iterate to one of the kernel

The minorisation of Theorem 1.2 is one of `κ^{2N}`, not of `κ`, and the excursion above wants
a one-step bound.  The gap is closed by averaging: if `μ` is invariant for `κⁿ` then so is
`(1/n) ∑_{i<n} μ κ^i` for `κ`, because the sum telescopes and the two ends agree. -/

section Average

/-- One step of the kernel after `n`, one point at a time. -/
theorem iterateKernel_succ_apply (κ : Kernel α α) (n : ℕ) (x : α) {A : Set α}
    (hA : MeasurableSet A) :
    iterateKernel κ (n + 1) x A = ∑' y : α, κ y A * iterateKernel κ n x {y} := by
  rw [iterateKernel_succ, Kernel.comp_apply' _ _ _ hA, lintegral_countable']

/-- The Cesàro average of the first `n` iterates, one point at a time. -/
noncomputable def avgFun (κ : Kernel α α) (n : ℕ) (μ : Measure α) (y : α) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range n, ∑' x : α, iterateKernel κ i x {y} * μ {x}

theorem tsum_avgFun (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) (μ : Measure α)
    [IsProbabilityMeasure μ] : ∑' y : α, avgFun κ n μ y = n := by
  have h : ∑' y : α, avgFun κ n μ y
      = ∑ i ∈ Finset.range n, ∑' y : α, ∑' x : α, iterateKernel κ i x {y} * μ {x} :=
    Summable.tsum_finsetSum fun i _ => ENNReal.summable
  have h2 : ∀ i : ℕ, ∑' y : α, ∑' x : α, iterateKernel κ i x {y} * μ {x} = 1 := by
    intro i
    rw [ENNReal.tsum_comm]
    have h3 : ∀ x : α, ∑' y : α, iterateKernel κ i x {y} * μ {x} = μ {x} := fun x => by
      rw [ENNReal.tsum_mul_right, tsum_measure_singleton (iterateKernel κ i x), one_mul]
    rw [tsum_congr h3, tsum_measure_singleton μ]
  rw [h, Finset.sum_congr rfl fun i _ => h2 i]
  simp

/-- **The average is invariant.**  The two ends of the telescoping sum agree, one by
`κ⁰ = id` and the other by the invariance of `μ` for `κⁿ`. -/
theorem tsum_avgFun_mul (κ : Kernel α α) [IsMarkovKernel κ] {n : ℕ} {μ : Measure α}
    [IsProbabilityMeasure μ] (hμ : Kernel.Invariant (iterateKernel κ n) μ) (y : α) :
    ∑' x : α, avgFun κ n μ x * κ x {y} = avgFun κ n μ y := by
  set B : ℕ → ℝ≥0∞ := fun i => ∑' z : α, iterateKernel κ i z {y} * μ {z} with hB
  have hstep : ∑' x : α, avgFun κ n μ x * κ x {y} = ∑ i ∈ Finset.range n, B (i + 1) := by
    have h1 : ∀ x : α, avgFun κ n μ x * κ x {y}
        = ∑ i ∈ Finset.range n, (∑' z : α, iterateKernel κ i z {x} * μ {z}) * κ x {y} :=
      fun x => Finset.sum_mul _ _ _
    rw [tsum_congr h1, Summable.tsum_finsetSum fun i _ => ENNReal.summable]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑' x : α, (∑' z : α, iterateKernel κ i z {x} * μ {z}) * κ x {y}
        = ∑' x : α, ∑' z : α, iterateKernel κ i z {x} * μ {z} * κ x {y} :=
          tsum_congr fun x => ENNReal.tsum_mul_right.symm
      _ = ∑' z : α, ∑' x : α, iterateKernel κ i z {x} * μ {z} * κ x {y} := ENNReal.tsum_comm
      _ = ∑' z : α, (∑' x : α, κ x {y} * iterateKernel κ i z {x}) * μ {z} := by
          refine tsum_congr fun z => ?_
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun x => by ring
      _ = B (i + 1) := by
          refine tsum_congr fun z => ?_
          rw [← iterateKernel_succ_apply κ i z (MeasurableSet.singleton y)]
  have hzero : B 0 = μ {y} := by
    have h0 : Kernel.Invariant (iterateKernel κ 0) μ := by
      rw [iterateKernel_zero]
      exact Measure.id_comp
    exact (measure_singleton_of_invariant (iterateKernel κ 0) h0 y).symm
  have hlast : B n = μ {y} := (measure_singleton_of_invariant (iterateKernel κ n) hμ y).symm
  have hB0 : B 0 ≠ ∞ := by
    rw [hzero]
    exact measure_ne_top μ _
  have htel : (∑ i ∈ Finset.range n, B (i + 1)) + B 0 = (∑ i ∈ Finset.range n, B i) + B 0 := by
    rw [← Finset.sum_range_succ' B n, Finset.sum_range_succ B n, hlast, hzero]
  rw [hstep, avgFun]
  refine le_antisymm ((ENNReal.add_le_add_iff_right hB0).1 htel.le)
    ((ENNReal.add_le_add_iff_right hB0).1 htel.ge)

variable {S : Set α}

/-- An absorbing set is absorbing for every iterate. -/
theorem iterateKernel_absorbing (κ : Kernel α α) (habs : ∀ x ∈ S, κ x Sᶜ = 0) :
    ∀ (i : ℕ), ∀ x ∈ S, iterateKernel κ i x Sᶜ = 0 := by
  intro i
  induction i with
  | zero =>
      intro x hx
      rw [iterateKernel_zero, Kernel.id_apply, Measure.dirac_apply' _ MeasurableSet.of_discrete]
      exact Set.indicator_of_notMem (by simpa using hx) _
  | succ i ih =>
      intro x hx
      rw [iterateKernel_succ_apply κ i x MeasurableSet.of_discrete]
      refine ENNReal.tsum_eq_zero.2 fun z => ?_
      by_cases hz : z ∈ S
      · rw [habs z hz, zero_mul]
      · rw [measure_mono_null (Set.singleton_subset_iff.2 hz) (ih x hx), mul_zero]

/-- The average stays inside an absorbing set. -/
theorem avgFun_eq_zero_of_notMem (κ : Kernel α α) {n : ℕ} {μ : Measure α} (hμS : μ Sᶜ = 0)
    (habs : ∀ x ∈ S, κ x Sᶜ = 0) {y : α} (hy : y ∉ S) : avgFun κ n μ y = 0 := by
  refine Finset.sum_eq_zero fun i _ => ENNReal.tsum_eq_zero.2 fun x => ?_
  by_cases hx : x ∈ S
  · rw [measure_mono_null (Set.singleton_subset_iff.2 hy)
      (iterateKernel_absorbing κ habs i x hx), zero_mul]
  · rw [measure_mono_null (Set.singleton_subset_iff.2 hx) hμS, mul_zero]

end Average

/-! ### The criterion, both halves -/

section Criterion

variable {S : Set α} {l : α} {c : ℝ≥0∞}

/-- Averaging turns an invariant probability measure of `κⁿ` into one of `κ`. -/
theorem exists_invariant_of_invariant_iterateKernel (κ : Kernel α α) [IsMarkovKernel κ]
    {n : ℕ} (hn : 0 < n) {μ : Measure α} [IsProbabilityMeasure μ] (hμS : μ Sᶜ = 0)
    (habs : ∀ x ∈ S, κ x Sᶜ = 0) (hμ : Kernel.Invariant (iterateKernel κ n) μ) :
    ∃ ρ : Measure α, IsProbabilityMeasure ρ ∧ ρ Sᶜ = 0 ∧ Kernel.Invariant κ ρ := by
  refine exists_invariant_of_weight κ (avgFun κ n μ) ?_ ?_
    (fun y hy => avgFun_eq_zero_of_notMem κ hμS habs hy) (tsum_avgFun_mul κ hμ)
  · rw [tsum_avgFun]
    exact_mod_cast hn.ne'
  · rw [tsum_avgFun]
    exact ENNReal.natCast_ne_top n

/-- **Doeblin's criterion, the existence half.**  A minorisation of the `n`-step kernel at a
single state, uniform over an absorbing set containing it, gives an invariant probability
measure carried by that set.

The `n`-step minorisation is reduced to a one-step one by looking at `κⁿ`, whose invariant
measures are averaged back into an invariant measure of `κ`. -/
theorem exists_invariant_of_iterate_minorisation (κ : Kernel α α) [IsMarkovKernel κ] {n : ℕ}
    (hn : 0 < n) (hc : 0 < c) (hlS : l ∈ S) (habs : ∀ x ∈ S, κ x Sᶜ = 0)
    (hmin : ∀ x ∈ S, c ≤ iterateKernel κ n x {l}) :
    ∃ μ : Measure α, IsProbabilityMeasure μ ∧ μ Sᶜ = 0 ∧ Kernel.Invariant κ μ := by
  obtain ⟨μ, hμp, hμS, hμinv⟩ := exists_invariant_of_minorisation (iterateKernel κ n) hc hlS
    (iterateKernel_absorbing κ habs n) hmin
  have := hμp
  exact exists_invariant_of_invariant_iterateKernel κ hn hμS habs hμinv

/-- **Doeblin's criterion.**  A Markov kernel on a countable space whose `n`-step kernel is
bounded below at a single state by `c > 0`, uniformly over an absorbing set carrying the
measures, has exactly one invariant probability measure carried by that set.

No irreducibility, no aperiodicity, no recurrence theory, and nothing imported beyond
`Kernel.Invariant`: uniqueness is the coupling argument of
`SocialNetwork.eq_of_invariant_of_minorisation_on`, and existence is the excursion measure of
`SocialNetwork.excursionFun`. -/
theorem existsUnique_invariant_of_iterate_minorisation (κ : Kernel α α) [IsMarkovKernel κ]
    {n : ℕ} (hn : 0 < n) (hc : 0 < c) (hlS : l ∈ S) (habs : ∀ x ∈ S, κ x Sᶜ = 0)
    (hmin : ∀ x ∈ S, c ≤ iterateKernel κ n x {l}) :
    ∃! μ : Measure α, IsProbabilityMeasure μ ∧ μ Sᶜ = 0 ∧ Kernel.Invariant κ μ := by
  obtain ⟨μ, hμp, hμS, hμinv⟩ := exists_invariant_of_iterate_minorisation κ hn hc hlS habs hmin
  refine ⟨μ, ⟨hμp, hμS, hμinv⟩, ?_⟩
  rintro ν ⟨hνp, hνS, hνinv⟩
  have := hμp
  have := hνp
  exact eq_of_invariant_of_iterate_minorisation κ n hc hmin hνS hμS hνinv hμinv

end Criterion

end SocialNetwork
