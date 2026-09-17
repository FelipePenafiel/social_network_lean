/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import Mathlib.Probability.Kernel.Invariance
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

/-- The invariance equation in coordinates: `μ {y} = ∑ₓ p (x, y) μ {x}`. -/
theorem measure_singleton_of_invariant (κ : Kernel α α) {μ : Measure α}
    (hμ : Kernel.Invariant κ μ) (y : α) : μ {y} = ∑' x : α, κ x {y} * μ {x} := by
  conv_lhs => rw [← hμ.def]
  rw [Measure.bind_apply (MeasurableSet.singleton y) (Kernel.aemeasurable _),
    lintegral_countable']

/-! ### The `n`-step kernel -/

/-- The `n`-step kernel `κⁿ`.  Doeblin's hypothesis is a minorisation of one of these, not of
`κ` itself: for the skeleton chain it is the `2N`-step kernel that [GL24] bounds below. -/
noncomputable def iterateKernel (κ : Kernel α α) : ℕ → Kernel α α
  | 0 => Kernel.id
  | n + 1 => κ ∘ₖ iterateKernel κ n

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

end SocialNetwork
