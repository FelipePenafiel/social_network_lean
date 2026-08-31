/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Skeleton
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The continuous-time process of equation (3)

Formalisation of the Markov jump process `(U_t^{β,u})_{t ≥ 0}` of arXiv:2607.19651, of its
generator (equation (3)), and of the statements of the paper that speak about it: Theorem 1,
Theorem 2, Theorem 3 and the auxiliary results of Sections 5.1–5.3.

## What is built, and what is only stated

Everything that is a *definition* is built for real.  Mathlib has no theory of continuous-time
Markov jump processes on a countable state space, but it does not need to have one for the
process itself to exist: the jump-hold representation is a discrete-time chain in disguise.
Driving the chain with the pairs

```
(Aₙ, Oₙ, holding time)   ∈   Jump N M × ℝ
```

and appealing to `ProbabilityTheory.Kernel.traj` gives the law of the whole realisation, from
which the jump times `Tₙ`, the process `U_t`, the hitting times `R^{β,u} (θ)` and the
transition semigroup are all definable.  That is what this file does.

What Mathlib does not have, and what this file therefore only *states*, is the analysis:
non-explosion (Theorem 1.1), existence and uniqueness of the invariant measure (Theorem 1.2,
which needs a Doeblin minorisation), the concentration of that measure (Theorem 2) and the
metastability estimate (Theorem 3).  Those carry a `sorry`.  See `blueprint/blueprint.md`.

## Main definitions

* `SocialNetwork.totalRate` — the paper's `q_β (v) = ∑_{a,o} exp (β u (a, o))`.
* `SocialNetwork.generator` — the generator `G` of equation (3).
* `SocialNetwork.ctsPathMeasure` — the law of a realisation `(Aₙ, Oₙ, holding time)ₙ`.
* `SocialNetwork.jumpTime` — the jump times `Tₙ`, with `T₀ = 0`.
* `SocialNetwork.process` — the process `U_t^{β,u}` itself.
* `SocialNetwork.transitionKernel` — the transition semigroup `P_t`.
* `SocialNetwork.hittingTimeCts` — the hitting time `R^{β,u} (θ) = inf {t ≥ 0 : U_t ∈ θ}`.

## Main statements

* `SocialNetwork.generator_eq`, `SocialNetwork.generator_const` — the algebra of `G`, proved.
* `SocialNetwork.nonExplosion` — **Theorem 1.1**, unproved.
* `SocialNetwork.existsUnique_invariantCts` — **Theorem 1.2**, unproved.
* `SocialNetwork.measure_ladderSet_ge` — **Theorem 2.1**, unproved.
* `SocialNetwork.tendsto_hittingTime_ladderSet` — **Theorem 2.2**, unproved.
* `SocialNetwork.metastability` — **Theorem 3**, unproved.
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The total jump rate and the generator of equation (3) -/

section Generator

/-- The total jump rate `q_β (v) = ∑_{(a,o)} exp (β u (a, o))` out of the matrix `v`, written
in the scaled coordinates of `SocialNetwork.Defs`.  This is the quantity that appears in the
transfer `μ^β ∝ μ̃^β / q_β` of equation (13). -/
noncomputable def totalRate (β : ℝ) (v : Pressure N M) : ℝ :=
  ∑ p : Jump N M, jumpRate β v p.1 p.2

theorem totalRate_nonneg (β : ℝ) (v : Pressure N M) : 0 ≤ totalRate β v :=
  Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le

variable [NeZero N] [NeZero M]

theorem totalRate_pos (β : ℝ) (v : Pressure N M) : 0 < totalRate β v :=
  Finset.sum_pos (fun p _ => jumpRate_pos β v p.1 p.2) (univ_jump_nonempty N M)

theorem totalRate_ne_zero (β : ℝ) (v : Pressure N M) : totalRate β v ≠ 0 :=
  (totalRate_pos β v).ne'

end Generator

section GeneratorDef

/-- **Equation (3).** The generator of the Markov jump process:

```
G f (u) = ∑_{o ∈ O} ∑_{a ∈ A} exp (β u (a, o)) [f (π^{a,o} (u)) - f (u)].
```

Written in scaled coordinates, so `exp (β u (a, o))` is `jumpRate β v a o`.  The paper takes
`f` bounded; boundedness plays no role in the identities below, so it is not required here. -/
noncomputable def generator (β : ℝ) (f : Pressure N M → ℝ) (v : Pressure N M) : ℝ :=
  ∑ p : Jump N M, jumpRate β v p.1 p.2 * (f (express p.1 p.2 v) - f v)

/-- The generator, with the two terms of equation (3) separated: the rate-weighted average of
the values after one expression, minus the total rate times the value at `v`. -/
theorem generator_eq (β : ℝ) (f : Pressure N M → ℝ) (v : Pressure N M) :
    generator β f v
      = (∑ p : Jump N M, jumpRate β v p.1 p.2 * f (express p.1 p.2 v)) - totalRate β v * f v := by
  rw [generator, totalRate, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The generator annihilates the constants, as any Markov generator must. -/
@[simp]
theorem generator_const (β : ℝ) (c : ℝ) (v : Pressure N M) :
    generator β (fun _ => c) v = 0 := by
  simp [generator]

theorem generator_add (β : ℝ) (f g : Pressure N M → ℝ) (v : Pressure N M) :
    generator β (fun w => f w + g w) v = generator β f v + generator β g v := by
  rw [generator, generator, generator, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem generator_smul (β : ℝ) (c : ℝ) (f : Pressure N M → ℝ) (v : Pressure N M) :
    generator β (fun w => c * f w) v = c * generator β f v := by
  rw [generator, generator, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

end GeneratorDef

/-! ### The jump-hold representation

A realisation of the process is the sequence of expressed pairs together with the holding
times between consecutive expressions.  Given that the matrix at time `T_{n-1}` is `v`, the
pair `(Aₙ, Oₙ)` follows `jumpPMF β v` and the holding time is exponential of rate `q_β (v)`,
independently.  That is exactly the content of equation (3). -/

section Steps

/-- One step of a realisation: which actor expressed which opinion, and how long the process
then waited before the next expression. -/
abbrev Step (N M : ℕ) := Jump N M × ℝ

namespace Trajectory

/-- The expressed pairs of a realisation, forgetting the holding times. -/
def ofStepPath (ω : ℕ → Step N M) : Trajectory N M := ofPath fun n => (ω n).1

/-- The expressed pairs of a finite history, forgetting the holding times. -/
def ofStepHistory {n : ℕ} (h : (i : Finset.Iic n) → Step N M) : Trajectory N M :=
  ofHistory fun i => (h i).1

end Trajectory

/-- Forgetting the holding times of a finite history is measurable. -/
theorem measurable_stepHistoryJumps (n : ℕ) :
    Measurable fun (h : (i : Finset.Iic n) → Step N M) (i : Finset.Iic n) => (h i).1 :=
  measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)

/-- The matrix reached after replaying a finite history is a measurable function of it: it
depends only on the expressed pairs, which live in a countable discrete space. -/
theorem measurable_stepHistoryState (u : Pressure N M) (n k : ℕ) :
    Measurable fun h : (i : Finset.Iic n) → Step N M =>
      (Trajectory.ofStepHistory h).state u k :=
  (Measurable.of_discrete
      (f := fun h : (i : Finset.Iic n) → Jump N M => (Trajectory.ofHistory h).state u k)).comp
    (measurable_stepHistoryJumps n)

variable [NeZero N] [NeZero M]

/-- The law of one step of the process from the matrix `v`: the expressed pair follows the
Gibbs law of equation (3), and the holding time is exponential with the total rate `q_β (v)`,
independently of it. -/
noncomputable def stepLaw (β : ℝ) (v : Pressure N M) : Measure (Step N M) :=
  (jumpPMF β v).toMeasure.prod (expMeasure (totalRate β v))

instance isProbabilityMeasure_stepLaw (β : ℝ) (v : Pressure N M) :
    IsProbabilityMeasure (stepLaw β v) := by
  have : IsProbabilityMeasure (expMeasure (totalRate β v)) :=
    isProbabilityMeasure_expMeasure (totalRate_pos β v)
  exact Measure.prod.instIsProbabilityMeasure _ _

/-- The kernel driving the continuous-time process: from the first `n + 1` steps, replay the
expressed pairs to find the current matrix, and read off the law of the next step.

Measurability is not automatic here — unlike in `SocialNetwork.Skeleton`, the sample space is
no longer countable, since it carries the real holding times — but it is still cheap: the law
of the next step depends on the history only through the matrix it reaches, which lives in a
countable discrete space. -/
noncomputable def ctsDrivingKernel (β : ℝ) (u : Pressure N M) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Step N M) (Step N M) where
  toFun h := stepLaw β ((Trajectory.ofStepHistory h).state u (n + 1))
  measurable' :=
    (Measurable.of_discrete (f := fun v : Pressure N M => stepLaw β v)).comp
      (measurable_stepHistoryState u n (n + 1))

theorem ctsDrivingKernel_apply (β : ℝ) (u : Pressure N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Step N M) :
    ctsDrivingKernel β u n h = stepLaw β ((Trajectory.ofStepHistory h).state u (n + 1)) := rfl

instance isMarkovKernel_ctsDrivingKernel (β : ℝ) (u : Pressure N M) (n : ℕ) :
    IsMarkovKernel (ctsDrivingKernel β u n) :=
  ⟨fun h => by rw [ctsDrivingKernel_apply]; infer_instance⟩

/-- The first step, read as a history of length one. -/
def toStepHistoryZero (z : Step N M) : (i : Finset.Iic 0) → Step N M := fun _ => z

omit [NeZero N] [NeZero M] in
theorem measurable_toStepHistoryZero :
    Measurable (toStepHistoryZero (N := N) (M := M)) :=
  measurable_pi_lambda _ fun _ => measurable_id

/-- The law of a realisation of the continuous-time process started at `u`: the sequence of
expressed pairs together with the holding times.  Its existence is the Ionescu-Tulcea theorem,
`ProbabilityTheory.Kernel.traj`. -/
noncomputable def ctsPathMeasure (β : ℝ) (u : Pressure N M) : Measure (ℕ → Step N M) :=
  Kernel.traj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0 ∘ₘ
    ((stepLaw β u).map toStepHistoryZero)

instance isProbabilityMeasure_ctsPathMeasure (β : ℝ) (u : Pressure N M) :
    IsProbabilityMeasure (ctsPathMeasure β u) := by
  rw [ctsPathMeasure]
  have : IsProbabilityMeasure ((stepLaw β u).map (toStepHistoryZero (N := N) (M := M))) :=
    Measure.isProbabilityMeasure_map measurable_toStepHistoryZero.aemeasurable
  infer_instance

end Steps

/-! ### Jump times, the process, and the hitting times -/

section Process

/-- The holding time between the `(n+1)`-st and the `(n+2)`-nd expression. -/
def holdingTime (n : ℕ) (ω : ℕ → Step N M) : ℝ := (ω n).2

theorem measurable_holdingTime (n : ℕ) : Measurable (holdingTime (N := N) (M := M) n) :=
  measurable_snd.comp (measurable_pi_apply n)

/-- The jump times `Tₙ` of the paper, with the convention `T₀ = 0`, so that `Tₙ` is the time
of the `n`-th expression. -/
noncomputable def jumpTime (n : ℕ) (ω : ℕ → Step N M) : ℝ :=
  ∑ k ∈ Finset.range n, holdingTime k ω

@[simp]
theorem jumpTime_zero (ω : ℕ → Step N M) : jumpTime 0 ω = 0 := by simp [jumpTime]

theorem jumpTime_succ (n : ℕ) (ω : ℕ → Step N M) :
    jumpTime (n + 1) ω = jumpTime n ω + holdingTime n ω :=
  Finset.sum_range_succ _ n

theorem measurable_jumpTime (n : ℕ) : Measurable (jumpTime (N := N) (M := M) n) :=
  Finset.measurable_sum _ fun k _ => measurable_holdingTime k

/-- `sup {Tₘ : m ≥ 1}`, the explosion time.  Theorem 1.1 says that it is infinite almost
surely, which is what makes the process well defined for every `t ≥ 0`. -/
noncomputable def explosionTime (ω : ℕ → Step N M) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (jumpTime n ω)

/-- The number of expressions that have occurred by time `t`.

On the explosion event this is junk — an unbounded set of naturals has no supremum — which is
harmless: `SocialNetwork.nonExplosion` says that event is null, and the paper likewise defines
the process only up to the explosion time. -/
noncomputable def jumpCount (ω : ℕ → Step N M) (t : ℝ) : ℕ :=
  sSup {n : ℕ | jumpTime n ω ≤ t}

/-- The process `U_t^{β,u}` of the paper: the matrix reached after the expressions that have
occurred by time `t`. -/
noncomputable def process (u : Pressure N M) (t : ℝ) (ω : ℕ → Step N M) : Pressure N M :=
  (Trajectory.ofStepPath ω).state u (jumpCount ω t)

@[simp]
theorem process_zero_of_nonneg (u : Pressure N M) (ω : ℕ → Step N M) :
    process u 0 ω = (Trajectory.ofStepPath ω).state u (jumpCount ω 0) := rfl

/-- `jumpCount ω t = k`, for `k ≠ 0`, exactly when `T_k ≤ t` and no jump time beyond the
`k`-th is `≤ t`.

**No counterpart in the paper**: this is an artefact of how the process is built here, the
jump-hold representation together with the junk `sSup` returns outside its intended range.

The restriction to `k ≠ 0` is not an artefact: `sSup` returns `0` on the empty set *and* on an
unbounded one, so `jumpCount ω t = 0` also records the explosion event, and there is no such
characterisation of it. -/
theorem jumpCount_eq_iff (t : ℝ) (ω : ℕ → Step N M) {k : ℕ} (hk : k ≠ 0) :
    jumpCount ω t = k ↔ jumpTime k ω ≤ t ∧ ∀ m : ℕ, jumpTime m ω ≤ t → m ≤ k := by
  simp only [jumpCount, Set.mem_setOf_eq]
  constructor
  · intro h
    have hbdd : BddAbove {n : ℕ | jumpTime n ω ≤ t} := by
      by_contra hb
      rw [Nat.sSup_of_not_bddAbove hb] at h
      exact hk h.symm
    have hne : {n : ℕ | jumpTime n ω ≤ t}.Nonempty := by
      rcases Set.eq_empty_or_nonempty {n : ℕ | jumpTime n ω ≤ t} with he | hn
      · exact absurd (by rw [← h, he]; simp) hk
      · exact hn
    have hmem := Nat.sSup_mem hne hbdd
    rw [h] at hmem
    exact ⟨hmem, fun m hm => by rw [← h]; exact le_csSup hbdd hm⟩
  · rintro ⟨hmem, hub⟩
    have hbdd : BddAbove {n : ℕ | jumpTime n ω ≤ t} := ⟨k, fun m hm => hub m hm⟩
    exact le_antisymm (csSup_le ⟨k, hmem⟩ fun m hm => hub m hm) (le_csSup hbdd hmem)

/-- Each level set of `jumpCount` is a countable Boolean combination of the events
`{Tₘ ≤ t}`, hence measurable. -/
theorem measurableSet_jumpCount_eq (t : ℝ) {k : ℕ} (hk : k ≠ 0) :
    MeasurableSet {ω : ℕ → Step N M | jumpCount ω t = k} := by
  have hset : {ω : ℕ → Step N M | jumpCount ω t = k}
      = {ω : ℕ → Step N M | jumpTime k ω ≤ t} ∩
        ⋂ m : ℕ, {ω : ℕ → Step N M | m ≤ k ∨ t < jumpTime m ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, jumpCount_eq_iff t ω hk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun m => (le_or_gt (jumpTime m ω) t).imp (h2 m) id⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun m hm => ?_⟩
      rcases h2 m with h | h
      · exact h
      · exact absurd hm (not_le.2 h)
  rw [hset]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun m => ?_)
  · have h : {ω : ℕ → Step N M | jumpTime k ω ≤ t}
        = jumpTime (N := N) (M := M) k ⁻¹' Set.Iic t := rfl
    rw [h]
    exact measurable_jumpTime k measurableSet_Iic
  · rcases le_or_gt m k with hm | hm
    · have h : {ω : ℕ → Step N M | m ≤ k ∨ t < jumpTime m ω} = Set.univ := by
        ext ω; simp [hm]
      rw [h]
      exact MeasurableSet.univ
    · have h : {ω : ℕ → Step N M | m ≤ k ∨ t < jumpTime m ω}
          = jumpTime (N := N) (M := M) m ⁻¹' Set.Ioi t := by
        ext ω; simp [Nat.not_le.2 hm]
      rw [h]
      exact measurable_jumpTime m measurableSet_Ioi

theorem measurable_jumpCount (t : ℝ) :
    Measurable fun ω : ℕ → Step N M => jumpCount ω t := by
  refine measurable_to_countable' fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · have h : (fun ω : ℕ → Step N M => jumpCount ω t) ⁻¹' {0}
        = (⋃ j : ℕ, {ω : ℕ → Step N M | jumpCount ω t = j + 1})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists]
      constructor
      · intro h j; omega
      · intro h
        by_contra hne
        exact h (jumpCount ω t - 1) (by omega)
    rw [h]
    exact (MeasurableSet.iUnion fun j =>
      measurableSet_jumpCount_eq t (show j + 1 ≠ 0 by omega)).compl
  · exact measurableSet_jumpCount_eq t hk

/-- The matrix after `k` expressions only reads the first `k + 1` steps, which live in a
finite discrete space, so it is a measurable function of the realisation. -/
theorem measurable_state_ofStepPath (u : Pressure N M) (k : ℕ) :
    Measurable fun ω : ℕ → Step N M => (Trajectory.ofStepPath ω).state u k := by
  have h : (fun ω : ℕ → Step N M => (Trajectory.ofStepPath ω).state u k)
      = (fun h : (i : Finset.Iic k) → Step N M => (Trajectory.ofStepHistory h).state u k) ∘
        Preorder.frestrictLe (π := fun _ : ℕ => Step N M) k := by
    funext ω
    exact (Trajectory.state_ofHistory_frestrictLe u (fun n => (ω n).1) (Nat.le_succ k)).symm
  rw [h]
  exact (measurable_stepHistoryState u k k).comp (Preorder.measurable_frestrictLe k)

/-- The process is a measurable function of the realisation.

**No counterpart in the paper**, which does not address measurability; what follows is the
formalisation's own argument, not a formalisation of anything written there.

`jumpCount` is a countable Boolean combination of the measurable events `{Tₙ ≤ t}`, so it is
measurable into the countable discrete space `ℕ`; the matrix after a fixed number of
expressions is measurable by `SocialNetwork.measurable_state_ofStepPath`; and the two combine
because the index they are glued along is countable. -/
theorem measurable_process (u : Pressure N M) (t : ℝ) :
    Measurable (process (N := N) (M := M) u t) := by
  have hpair : Measurable
      fun p : ℕ × (ℕ → Step N M) => (Trajectory.ofStepPath p.2).state u p.1 :=
    measurable_from_prod_countable_right fun k => measurable_state_ofStepPath u k
  have h : process (N := N) (M := M) u t
      = (fun p : ℕ × (ℕ → Step N M) => (Trajectory.ofStepPath p.2).state u p.1) ∘
        fun ω : ℕ → Step N M => (jumpCount ω t, ω) := rfl
  rw [h]
  exact hpair.comp ((measurable_jumpCount t).prodMk measurable_id)

/-- The hitting time `R^{β,u} (θ) = inf {t ≥ 0 : U_t^{β,u} ∈ θ}` of the paper, valued in
`ℝ≥0∞` so that `⊤` records that `θ` is never reached. -/
noncomputable def hittingTimeCts (u : Pressure N M) (θ : Set (Pressure N M))
    (ω : ℕ → Step N M) : ℝ≥0∞ :=
  sInf ((fun t : ℝ => ENNReal.ofReal t) '' {t : ℝ | 0 ≤ t ∧ process u t ω ∈ θ})

/-- **Unproved, and not routine after all.**  The blueprint listed this next to
`SocialNetwork.measurable_process`, on the grounds that both only see `jumpCount`.  They do
not sit at the same depth.  `process` is an infimum over nothing: it is evaluated at one `t`.
This one is an infimum over the *uncountable* family `{t : 0 ≤ t}`, so it needs the path
`t ↦ U_t (ω)` to be right-continuous, which reduces the infimum to a countable one.

Right-continuity holds only where the jump times increase, and `holdingTime` is a plain real
coordinate: it is positive `ctsPathMeasure`-almost surely, since `expMeasure` charges only
`[0, ∞)`, but not for every `ω`.  On a realisation whose holding times are negative, or whose
jump times accumulate from the right at some `t`, `jumpCount ω ·` is not right-continuous and
the reduction fails pointwise.

So the statement wants either an almost-sure formulation, or a proof that goes through the
null set on which the path misbehaves.  Both are real work, and neither is the routine
cylinder argument the blueprint promised. -/
theorem measurable_hittingTimeCts (u : Pressure N M) (θ : Set (Pressure N M)) :
    Measurable (hittingTimeCts (N := N) (M := M) u θ) := by
  sorry

variable [NeZero N] [NeZero M]

/-- The law of the hitting time `R^{β,u} (θ)`, as a number: the probability, under the process
started at `u`, that `θ` has not been reached by time `t`. -/
noncomputable def probHittingGT (β : ℝ) (u : Pressure N M) (θ : Set (Pressure N M))
    (t : ℝ≥0∞) : ℝ≥0∞ :=
  ctsPathMeasure β u {ω | t < hittingTimeCts u θ ω}

/-- The expectation `E (R^{β,u} (θ))` appearing in Theorem 3. -/
noncomputable def expHittingTimeCts (β : ℝ) (u : Pressure N M) (θ : Set (Pressure N M)) :
    ℝ≥0∞ :=
  ∫⁻ ω, hittingTimeCts u θ ω ∂(ctsPathMeasure β u)

/-- The transition semigroup `P_t (v, ·)` of the process: the law of `U_t^{β,v}`. -/
noncomputable def transitionKernel (β : ℝ) (t : ℝ) : Kernel (Pressure N M) (Pressure N M) :=
  Kernel.ofFunOfCountable fun v => (ctsPathMeasure β v).map (process v t)

theorem transitionKernel_apply (β : ℝ) (t : ℝ) (v : Pressure N M) :
    transitionKernel β t v = (ctsPathMeasure β v).map (process v t) := rfl

instance isMarkovKernel_transitionKernel (β : ℝ) (t : ℝ) :
    IsMarkovKernel (transitionKernel (N := N) (M := M) β t) := by
  refine ⟨fun v => ?_⟩
  rw [transitionKernel_apply]
  exact Measure.isProbabilityMeasure_map (measurable_process v t).aemeasurable

end Process

/-! ### Invariant measures

A measure is invariant for the process when it is invariant for every `P_t`.  The paper's
`μ^β` is the unique invariant *probability* measure carried by the state space `S`, and its
skeleton counterpart `μ̃^β` of Definition 3 is the unique invariant probability measure of
`SocialNetwork.skeletonKernel`. -/

section Invariant

variable [NeZero N] [NeZero M]

/-- A measure is carried by the state space `S` of equation (2). -/
def IsCarriedByState (μ : Measure (Pressure N M)) : Prop := μ (stateSet N M)ᶜ = 0

/-- Invariance for the continuous-time process: invariance under every `P_t`, `t ≥ 0`. -/
def IsInvariantCts (β : ℝ) (μ : Measure (Pressure N M)) : Prop :=
  ∀ t : ℝ, 0 ≤ t → Kernel.Invariant (transitionKernel β t) μ

/-- **Theorem 1.1.** For any `β ≥ 0` and any starting matrix `u ∈ S`, the jump times satisfy
`P (sup {Tₘ : m ≥ 1} = ∞) = 1`: the process does not explode.

The paper's proof sandwiches the jump times between two Poisson processes, using Proposition 5
to control how often an expression comes from an actor carrying little pressure.  Mathlib has
no Poisson point process, so the comparison is not available. -/
theorem nonExplosion (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    (hu : IsState u) :
    ctsPathMeasure β u {ω | explosionTime ω = ⊤} = 1 := by
  sorry

/-- **Theorem 1.2.** The process has a unique invariant probability measure `μ^β`.

The paper obtains it from the skeleton: a uniform Doeblin minorisation gives the skeleton a
unique invariant measure `μ̃^β`, which is then transferred by equation (13).  Mathlib has
neither the minorisation criterion nor the transfer. -/
theorem existsUnique_invariantCts (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    ∃! μ : Measure (Pressure N M),
      IsProbabilityMeasure μ ∧ IsCarriedByState μ ∧ IsInvariantCts β μ := by
  sorry

/-- **Definition 3**, the invariant measure `μ̃^β` of the skeleton process.

Uniqueness is what Theorem 1.2 rests on, and it is the Doeblin step that is missing. -/
theorem existsUnique_invariantSkeleton (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    ∃! μ : Measure (Pressure N M),
      IsProbabilityMeasure μ ∧ IsCarriedByState μ ∧ Kernel.Invariant (skeletonKernel β) μ := by
  sorry

/-- **Equation (13)**, the transfer from the skeleton to continuous time:

```
μ^β (u) = (μ̃^β (u) / q_β (u)) / ∑_{v ∈ S} (μ̃^β (v) / q_β (v)).
```

This is the correspondence that makes the two invariant measures determine each other; the
paper notes that it is a bijection between the stationary laws of the two processes. -/
theorem invariantCts_eq_of_invariantSkeleton (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {μ μskel : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ) (hμS : IsCarriedByState μ)
    (hμinv : IsInvariantCts β μ) (hs : IsProbabilityMeasure μskel)
    (hsS : IsCarriedByState μskel) (hsinv : Kernel.Invariant (skeletonKernel β) μskel)
    (v : Pressure N M) :
    μ {v} = (μskel {v} / ENNReal.ofReal (totalRate β v)) /
      ∑' w : Pressure N M, μskel {w} / ENNReal.ofReal (totalRate β w) := by
  sorry

end Invariant

/-! ### Theorem 2: concentration of the invariant measure on the ladder sets -/

section Theorem2

variable [NeZero N] [NeZero M]

/-- **Theorem 2.1.** There is a constant `C > 0` such that for every `β ≥ 0` the invariant
probability measure satisfies `μ^β (L) ≥ 1 - C e^{-β/(M-1)}`.

The paper proves it from Proposition 9 (the skeleton measure of a non-steep-ladder state is
exponentially small) together with the transfer of equation (13). -/
theorem measure_ladderSet_ge (hM : 2 ≤ M) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ μ : Measure (Pressure N M),
      IsProbabilityMeasure μ → IsCarriedByState μ → IsInvariantCts β μ →
        ENNReal.ofReal (1 - C * Real.exp (-β / ((M : ℝ) - 1))) ≤ μ (ladderSet N M) := by
  sorry

/-- **Theorem 2.2.** For every fixed `δ > 0`,

```
sup_{u ∈ S \ {0}} P (R^{β,u} (L) > e^{-β(1-δ)/(M-1)})  →  0   as β → +∞.
```

The zero matrix has to be excluded: from `0` every rate equals `1`, so the first expression
takes a time of order `1` rather than `e^{-β/(M-1)}`.  Corollary 11 is the version that covers
it, at the price of an extra exponential random variable. -/
theorem tendsto_hittingTime_ladderSet (hM : 2 ≤ M) (hN : 3 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun β : ℝ => ⨆ u ∈ (stateSet N M \ {0} : Set (Pressure N M)),
        probHittingGT β u (ladderSet N M)
          (ENNReal.ofReal (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))))
      Filter.atTop (nhds 0) := by
  sorry

/-- **Corollary 11.** From the zero matrix, the hitting time of `L` is bounded by an
exponential waiting time of mean `1/(MN)` plus the same `e^{-β(1-δ)/(M-1)}`. -/
theorem tendsto_hittingTime_ladderSet_zero (hM : 2 ≤ M) (hN : 3 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun β : ℝ => ⨆ s ∈ Set.Ici (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(((M * N : ℕ) : ℝ)) * s)) *
          probHittingGT β 0 (ladderSet N M)
            (ENNReal.ofReal (s + Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))))
      Filter.atTop (nhds 0) := by
  sorry

/-- **The bound displayed inside the proof of part 2 of Theorem 2.**  For any `u ∈ S \ {0}`
and any `t > 0`,

```
P (R^{β,u} (L) > t) ≤ 1 - ζ_β^{(M+1)N} + (M+1) N exp (-e^{β/(M-1)} t / ((M+1) N)).
```

**No counterpart among the numbered statements of the paper.**  Theorem 2.2 above --- the Lean
`SocialNetwork.tendsto_hittingTime_ladderSet` --- is the limit this inequality gives at
`t = e^{-β(1-δ)/(M-1)}`, and the inequality itself never becomes a statement.  Lemma 13 uses
the inequality and not the limit, so it cannot be derived from Theorem 2.2 as stated: taking
the limit has thrown the rate away.  The display is transcribed here so that Lemma 13 has
something to rest on; see `FOR-THE-AUTHORS.md`. -/
theorem probHittingGT_ladderSet_le_of_ne_zero (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {u : Pressure N M} (hu : IsState u) (hu0 : u ≠ 0) {t : ℝ} (ht : 0 < t) :
    probHittingGT β u (ladderSet N M) (ENNReal.ofReal t)
      ≤ ENNReal.ofReal (1 - zeta N M β ^ ((M + 1) * N)
          + (((M + 1) * N : ℕ) : ℝ) *
            Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * t) / (((M + 1) * N : ℕ) : ℝ))) := by
  sorry

/-- **Equation (19)**, the quantitative form of Corollary 11:

```
P (R^{β,0} (L) > 2β) ≤ P (τ > β) + sup_{u ≠ 0} P (R^{β,u} (L) > β),
```

with `τ` the waiting time before the first expression from the zero matrix.

**No counterpart among the numbered statements of the paper.**  Corollary 11 above --- the Lean
`SocialNetwork.tendsto_hittingTime_ladderSet_zero` --- is a limit, and this is the inequality
its proof gives; Lemma 13 uses the inequality.

`P (τ > β)` is written here as the paper evaluates it, `e^{-β/(MN)}`.  Note that `τ` is
declared exponential of mean `1/(MN)`, for which `P (τ > β) = e^{-MNβ}`; since
`e^{-MNβ} ≤ e^{-β/(MN)}` for `β ≥ 0`, the form written here is the weaker of the two, so
Lemma 13 follows from either reading. -/
theorem probHittingGT_ladderSet_zero_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    probHittingGT β 0 (ladderSet N M) (ENNReal.ofReal (2 * β))
      ≤ ENNReal.ofReal (Real.exp (-β / ((M * N : ℕ) : ℝ)))
        + ⨆ v ∈ (stateSet N M \ {0} : Set (Pressure N M)),
            probHittingGT β v (ladderSet N M) (ENNReal.ofReal β) := by
  sorry

/-- The arithmetic of the last line of the proof of Lemma 13: the three bounds the paper
collects fit under `(M+1)² N² e^{-β/((M+1)N)}`.  Each term is compared to that same
exponential --- `MN ≤ (M+1)N`, `M - 1 ≤ (M+1)N` and `e^{β/(M-1)} ≥ 1` --- leaving the
integer inequality `1 + (M+1)N ≤ (M+1)N²`, which holds since `N ≥ 3`.

**Supplies a step the paper asserts**: "putting the inequalities above together, we conclude
the proof". -/
theorem exp_add_zeta_pow_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-β / ((M * N : ℕ) : ℝ))
        + (1 - zeta N M β ^ ((M + 1) * N)
          + (((M + 1) * N : ℕ) : ℝ) *
            Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * β) / (((M + 1) * N : ℕ) : ℝ)))
      ≤ (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)) := by
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hKc : (((M + 1) * N : ℕ) : ℝ) = ((M : ℝ) + 1) * (N : ℝ) := by push_cast; ring
  have hMNc : ((M * N : ℕ) : ℝ) = (M : ℝ) * (N : ℝ) := by push_cast; ring
  have hKpos : (0 : ℝ) < ((M : ℝ) + 1) * (N : ℝ) := by nlinarith
  have hMNpos : (0 : ℝ) < (M : ℝ) * (N : ℝ) := by nlinarith
  have hM1pos : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hEpos : (0 : ℝ) < Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)) := Real.exp_pos _
  -- the waiting time from the zero matrix
  have h1 : Real.exp (-β / ((M * N : ℕ) : ℝ))
      ≤ Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)) := by
    refine Real.exp_le_exp.2 ?_
    rw [hMNc, hKc, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hβ hMNpos (by nlinarith)
  -- the greedy run, through Remark 4
  have h2 : 1 - zeta N M β ^ ((M + 1) * N)
      ≤ (((M + 1) * N : ℕ) : ℝ) * ((M : ℝ) * (N : ℝ))
          * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)) := by
    have hz := one_sub_le_zeta_pow N M β ((M + 1) * N)
    have hexp : Real.exp (-(β / ((M : ℝ) - 1)))
        ≤ Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)) := by
      refine Real.exp_le_exp.2 ?_
      rw [hKc, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left hβ hM1pos (by nlinarith)
    have hcoef : (0 : ℝ) ≤ (((M + 1) * N : ℕ) : ℝ) * ((M : ℝ) * (N : ℝ)) := by positivity
    nlinarith [hz, hexp, hcoef]
  -- the race between the exponential clocks
  have h3 : (((M + 1) * N : ℕ) : ℝ) *
        Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * β) / (((M + 1) * N : ℕ) : ℝ))
      ≤ (((M + 1) * N : ℕ) : ℝ) * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)) := by
    have hone : (1 : ℝ) ≤ Real.exp (β / ((M : ℝ) - 1)) :=
      Real.one_le_exp (by positivity)
    have hnum : -(Real.exp (β / ((M : ℝ) - 1)) * β) ≤ -β := by nlinarith
    have hstep : -(Real.exp (β / ((M : ℝ) - 1)) * β) / (((M + 1) * N : ℕ) : ℝ)
        ≤ -β / (((M + 1) * N : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right hnum
      rw [hKc]; exact hKpos.le
    have hKnn : (0 : ℝ) ≤ (((M + 1) * N : ℕ) : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hstep) hKnn
  -- the three constants fit
  have hfit : 1 + (((M + 1) * N : ℕ) : ℝ) * ((M : ℝ) * (N : ℝ)) + (((M + 1) * N : ℕ) : ℝ)
      ≤ (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith [hM2, hN3]
  have hcomb := mul_le_mul_of_nonneg_right hfit hEpos.le
  nlinarith [h1, h2, h3, hcomb]

/-- **Lemma 13.** For any `u ∈ S`,
`P (R^{β,u} (L) > 2β) ≤ (M+1)² N² e^{-β/((M+1)N)}`.

This is the form in which Theorem 2 feeds into the metastability estimate: it is assumption
(16) of Proposition 12, with `s₂ = 2β`. -/
theorem probHittingGT_ladderSet_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {u : Pressure N M} (hu : IsState u) :
    probHittingGT β u (ladderSet N M) (ENNReal.ofReal (2 * β))
      ≤ ENNReal.ofReal ((((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) *
          Real.exp (-β / (((M + 1) * N : ℕ) : ℝ))) := by
  rcases eq_or_lt_of_le hβ with hβ0 | hβpos
  · -- `β = 0`: the right-hand side is already at least one
    refine le_trans (prob_le_one (μ := ctsPathMeasure β u)) ?_
    rw [← hβ0]
    refine ENNReal.one_le_ofReal.2 ?_
    rw [neg_zero, zero_div, Real.exp_zero, mul_one]
    have hN0 : 0 < N := by omega
    have h1 : 1 ≤ ((M + 1) ^ 2 * N ^ 2 : ℕ) :=
      Nat.mul_pos (Nat.pow_pos (Nat.succ_pos M)) (Nat.pow_pos hN0)
    exact_mod_cast h1
  · -- the bound the proof of Theorem 2.2 puts on every non-null start
    set A : ℝ := 1 - zeta N M β ^ ((M + 1) * N)
        + (((M + 1) * N : ℕ) : ℝ) *
          Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * β) / (((M + 1) * N : ℕ) : ℝ)) with hA
    have hA0 : 0 ≤ A := by
      have hz1 : zeta N M β ^ ((M + 1) * N) ≤ 1 :=
        pow_le_one₀ (zeta_pos N M β).le (zeta_le_one N M β)
      have hrest : (0 : ℝ) ≤ (((M + 1) * N : ℕ) : ℝ) *
          Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * β) / (((M + 1) * N : ℕ) : ℝ)) := by
        positivity
      rw [hA]; linarith
    have hsup : (⨆ v ∈ (stateSet N M \ {0} : Set (Pressure N M)),
        probHittingGT β v (ladderSet N M) (ENNReal.ofReal β)) ≤ ENNReal.ofReal A := by
      refine iSup₂_le fun v hv => ?_
      rw [hA]
      exact probHittingGT_ladderSet_le_of_ne_zero hM hN hβ hv.1 hv.2 hβpos
    -- and the arithmetic that collects the pieces
    have hfin : ENNReal.ofReal (Real.exp (-β / ((M * N : ℕ) : ℝ))) + ENNReal.ofReal A
        ≤ ENNReal.ofReal ((((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) *
            Real.exp (-β / (((M + 1) * N : ℕ) : ℝ))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le hA0, hA]
      exact ENNReal.ofReal_le_ofReal (exp_add_zeta_pow_le hM hN hβ)
    by_cases hu0 : u = 0
    · -- from the zero matrix, through equation (19)
      subst hu0
      exact le_trans (le_trans (probHittingGT_ladderSet_zero_le hM hN hβ)
        (add_le_add le_rfl hsup)) hfin
    · -- from any other state the event at `2β` is contained in the event at `β`
      have hmono : probHittingGT β u (ladderSet N M) (ENNReal.ofReal (2 * β))
          ≤ probHittingGT β u (ladderSet N M) (ENNReal.ofReal β) :=
        measure_mono fun ω hω =>
          lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) hω
      refine le_trans hmono (le_trans ?_ hfin)
      refine le_trans ?_ (self_le_add_left (ENNReal.ofReal A) _)
      rw [hA]
      exact probHittingGT_ladderSet_le_of_ne_zero hM hN hβ hu hu0 hβpos

end Theorem2

/-! ### Theorem 3: metastability -/

section Theorem3

variable [NeZero N] [NeZero M]

/-- **Lemma 14.1.** From a ladder supporting `o`, the consensus for another opinion is not
reached before time `t` with probability at least `exp (-2 t N³ (M+1)³ e^{-β/(M-1)})`. -/
theorem le_probHittingGT_consensusOther (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsLadder o l) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Real.exp
        (-2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1))))
      ≤ probHittingGT β l (consensusSetOther N o) (ENNReal.ofReal t) := by
  sorry

/-- **Lemma 14.2.** From a consensus state for `o`, the consensus for another opinion is
reached before time `t` with probability at most `(N²M + 2 t N³ (M+1)³) e^{-β/(M-1)}`. -/
theorem probHittingLE_consensusOther_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {u : Pressure N M} (hu : IsConsensus o u) {t : ℝ} (ht : 0 < t) :
    ctsPathMeasure β u {ω | hittingTimeCts u (consensusSetOther N o) ω ≤ ENNReal.ofReal t}
      ≤ ENNReal.ofReal ((((N ^ 2 * M : ℕ) : ℝ) + 2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) *
          Real.exp (-β / ((M : ℝ) - 1))) := by
  sorry

/-- The characteristic time `c_β` of Section 5.3: the time at which the probability of not
having left the consensus set for `o` equals `e^{-1}`.  The paper notes that by symmetry it
does not depend on which ladder `l ∈ L^o` the process starts from. -/
def IsCharacteristicTime (β : ℝ) (o : Opinion M) (c : ℝ) : Prop :=
  0 < c ∧ ∀ l : Pressure N M, IsLadder o l →
    probHittingGT β l (consensusSetOther N o) (ENNReal.ofReal c)
      = ENNReal.ofReal (Real.exp (-1))

/-- **Corollary 15.** `c_β ≥ (1/2) N^{-3} (M+1)^{-3} e^{β/(M-1)}`: the characteristic time
grows exponentially in `β`, which is what makes the exit asymptotically exponential. -/
theorem le_characteristicTime (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {o : Opinion M}
    {c : ℝ} (hc : IsCharacteristicTime (N := N) β o c) :
    (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹ * Real.exp (β / ((M : ℝ) - 1)) ≤ c := by
  obtain ⟨hcpos, hchar⟩ := hc
  have hKpos : (0 : ℝ) < ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have hN0 : 0 < N := by omega
    exact_mod_cast Nat.mul_pos (Nat.pow_pos hN0) (Nat.pow_pos (Nat.succ_pos M))
  have h14 := le_probHittingGT_consensusOther hM hN hβ (isLadder_ladderOf (N := N) o) hcpos
  rw [hchar _ (isLadder_ladderOf (N := N) o)] at h14
  have h' := Real.exp_le_exp.mp
    ((ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h14)
  rw [neg_div, Real.exp_neg] at h'
  have hFpos : (0 : ℝ) < Real.exp (β / ((M : ℝ) - 1)) := Real.exp_pos _
  have key : (1 : ℝ) ≤ 2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) *
      (Real.exp (β / ((M : ℝ) - 1)))⁻¹ := by linarith
  have hFle : Real.exp (β / ((M : ℝ) - 1)) ≤ 2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right key hFpos.le
    rwa [one_mul, inv_mul_cancel_right₀ hFpos.ne'] at this
  have hKne : ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) ≠ 0 := hKpos.ne'
  have hstep := mul_le_mul_of_nonneg_left hFle
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹)
  rwa [show (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹ *
    (2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) = c by field_simp] at hstep

/-- Hitting a larger set happens no later. -/
theorem hittingTimeCts_mono (u : Pressure N M) {θ₁ θ₂ : Set (Pressure N M)} (h : θ₁ ⊆ θ₂)
    (ω : ℕ → Step N M) : hittingTimeCts u θ₂ ω ≤ hittingTimeCts u θ₁ ω :=
  sInf_le_sInf (Set.image_mono fun _ ht => ⟨ht.1, h ht.2⟩)

/-! #### The four assumptions of Proposition 12, for this model

Section 5.3 of the paper checks (15)–(18) in half a page, with the constants
`s₁ = 1`, `ε₁ = 2N³(M+1)³e^{-β/(M-1)}`, `s₂ = 2β`, `ε₂ = (M+1)²N²e^{-β/((M+1)N)}`,
`δ = 1/((M+1)N)`, `C = K = 8e^{-1}(M+1)⁴N³` and `θ = 1/(2(M-1))`.  Each is one lemma here. -/

/-- `x e^{-x} ≤ e^{-1}`: the calculus fact behind the paper's
`sup_{β ≥ 0} β e^{-β/(2(M-1))} = 2e^{-1}(M-1)`, used for (17) and (18).

**Supplies a step the paper asserts**, which states the supremum without proof. -/
theorem mul_exp_neg_le_exp_neg_one (x : ℝ) : x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h : x ≤ Real.exp (x - 1) := by have := Real.add_one_le_exp (x - 1); linarith
  calc x * Real.exp (-x) ≤ Real.exp (x - 1) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- The scaled form: `β e^{-β/a} ≤ a e^{-1}` for `a > 0`. -/
theorem mul_exp_neg_div_le {a : ℝ} (ha : 0 < a) (β : ℝ) :
    β * Real.exp (-β / a) ≤ a * Real.exp (-1) := by
  have h := mul_exp_neg_le_exp_neg_one (β / a)
  have ha' : a ≠ 0 := ha.ne'
  have hmul := mul_le_mul_of_nonneg_left h ha.le
  rw [show a * (β / a * Real.exp (-(β / a))) = β * Real.exp (-(β / a)) by field_simp] at hmul
  rw [show -β / a = -(β / a) by ring]
  exact hmul

variable [NeZero N] [NeZero M]

/-- Assumption **(16)** of Proposition 12, with `s₂ = 2β`.

The paper cites Lemma 13, which is about `L`, for a condition about `L^o ∪ C^{-o}`.
**Supplies a step the paper asserts**: the two are related by `L ⊆ L^o ∪ C^{-o}` — a ladder
for `p ≠ o` is a consensus state for `p` — so the hitting time of the larger set is smaller. -/
theorem probHittingGT_ladderOther_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (o : Opinion M) {u : Pressure N M} (hu : IsState u) :
    probHittingGT β u ({v | IsLadder o v} ∪ consensusSetOther N o) (ENNReal.ofReal (2 * β))
      ≤ ENNReal.ofReal ((((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) *
          Real.exp (-β / (((M + 1) * N : ℕ) : ℝ))) := by
  refine le_trans (measure_mono fun ω hω => ?_) (probHittingGT_ladderSet_le hM hN hβ hu)
  have hsub : ladderSet N M ⊆ {v | IsLadder o v} ∪ consensusSetOther N o := by
    rintro v ⟨p, hp⟩
    by_cases hpo : p = o
    · exact Or.inl (hpo ▸ hp)
    · exact Or.inr ⟨p, hpo, hp.isConsensus hM (by omega)⟩
  exact lt_of_lt_of_le hω (hittingTimeCts_mono u hsub ω)

/-- Assumption **(15)** of Proposition 12, with `s₁ = 1` and `ε₁ = 2N³(M+1)³e^{-β/(M-1)}`.

Part 1 of Lemma 14 at `t = 1` bounds the probability of *not* having left, so the bound on
`ε₁` is the complementary event; `1 - e^{-x} ≤ x` turns the exponential into the linear form
the paper quotes. -/
theorem measure_hittingTime_le_one (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsLadder o l) :
    ctsPathMeasure β l
        {ω | hittingTimeCts l (consensusSetOther N o) ω ≤ ENNReal.ofReal 1}
      ≤ ENNReal.ofReal (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) *
          Real.exp (-β / ((M : ℝ) - 1))) := by
  set E : ℝ := Real.exp (-β / ((M : ℝ) - 1)) with hE
  set Kc : ℝ := ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hE0 : 0 < E := Real.exp_pos _
  have hx0 : 0 ≤ 2 * Kc * E := by positivity
  -- the event and its complement
  have hmeas : MeasurableSet {ω : ℕ → Step N M |
      ENNReal.ofReal 1 < hittingTimeCts l (consensusSetOther N o) ω} :=
    measurableSet_lt measurable_const (measurable_hittingTimeCts l _)
  have hcompl : {ω : ℕ → Step N M |
      hittingTimeCts l (consensusSetOther N o) ω ≤ ENNReal.ofReal 1}
      = {ω : ℕ → Step N M |
        ENNReal.ofReal 1 < hittingTimeCts l (consensusSetOther N o) ω}ᶜ := by
    ext ω; simp [not_lt]
  -- Lemma 14.1 at t = 1
  have h14 := le_probHittingGT_consensusOther hM hN hβ hl (t := 1) one_pos
  rw [show (-2 * (1 : ℝ) * Kc * E) = -(2 * Kc * E) by ring] at h14
  rw [hcompl, prob_compl_eq_one_sub hmeas]
  refine le_trans (tsub_le_tsub_left h14 1) ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.add_one_le_exp (-(2 * Kc * E))
  linarith

/-- `e^{-β/a} ≤ a/β`, from `x ≤ e^x`.  Used to pin down a threshold `β₁` above which
`ε₁ + ε₂ ≤ 1/2`, the constraint the paper only asks to hold "for `β` sufficiently big". -/
theorem exp_neg_div_le {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : Real.exp (-β / a) ≤ a / β := by
  have hpos : 0 < β / a := div_pos hβ ha
  have h : β / a ≤ Real.exp (β / a) := by have := Real.add_one_le_exp (β / a); linarith
  have hinv : (Real.exp (β / a))⁻¹ ≤ (β / a)⁻¹ := inv_anti₀ hpos h
  rw [show -β / a = -(β / a) by ring, Real.exp_neg]
  rwa [inv_div] at hinv

/-- `1 ≤ 8 e^{-1}`, the only numeric fact the paper's constants rest on. -/
theorem one_le_eight_mul_exp_neg_one : (1 : ℝ) ≤ 8 * Real.exp (-1) := by
  have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 < 8 := lt_trans Real.exp_one_lt_three (by norm_num)
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ h2]
  linarith

/-- The size comparison behind the paper's constants: `N² M` and `(M+1)² N²` are both
dominated by `8 e^{-1} (M+1)⁴ N³`, with room to spare for the `(M-1)` term of (18). -/
theorem const_bounds (hM : 2 ≤ M) (hN : 3 ≤ N) :
    ((N ^ 2 * M : ℕ) : ℝ)
        + 8 * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1)
      ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ)
    ∧ 8 * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1)
      ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ)
    ∧ (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ)
      ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) := by
  have hn : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set e : ℝ := Real.exp (-1) with he'
  have he : (1 : ℝ) ≤ 8 * e := one_le_eight_mul_exp_neg_one
  have he0 : 0 < e := Real.exp_pos _
  have hP : (0 : ℝ) < (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := by positivity
  have hcube : (M : ℝ) ≤ ((M : ℝ) + 1) ^ 3 := by
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ (M:ℝ)) 3, sq_nonneg (M:ℝ)]
  have hpow : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by nlinarith
  have hdom : (N : ℝ) ^ 2 * (M : ℝ) ≤ (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := by nlinarith
  have hsq : ((M : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    have hsplit : 8 * e * ((M : ℝ) + 1) ^ 4 * (N : ℝ) ^ 3
        - 8 * e * ((N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3) * ((M : ℝ) - 1)
        = 16 * e * ((N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3) := by ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * e - 2) hP.le]
  · push_cast
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * e) hP.le)
      (by linarith : (0 : ℝ) ≤ 2)]
  · push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * e - 1) hP.le]

/-- Assumption **(18)** of Proposition 12, with `s₂ = 2β`, `θ = 1/(2(M-1))` and
`K = 8 e^{-1} (M+1)⁴ N³`.

Part 2 of Lemma 14 at `t = 2β` gives `(N²M + 4βN³(M+1)³) e^{-β/(M-1)}`; splitting the
exponent in half and absorbing `β e^{-β/(2(M-1))} ≤ 2(M-1)e^{-1}` is the paper's step (20). -/
theorem measure_hittingTime_le_two_mul (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    {o : Opinion M} {u : Pressure N M} (hu : IsConsensus o u) :
    ctsPathMeasure β u
        {ω | hittingTimeCts u (consensusSetOther N o) ω ≤ ENNReal.ofReal (2 * β)}
      ≤ ENNReal.ofReal (8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) *
          Real.exp (-(1 / (2 * ((M : ℝ) - 1))) * β)) := by
  refine le_trans (probHittingLE_consensusOther_le hM hN hβ.le hu (by linarith : (0:ℝ) < 2 * β))
    (ENNReal.ofReal_le_ofReal ?_)
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set a : ℝ := 2 * ((M : ℝ) - 1) with ha'
  have ha : 0 < a := by rw [ha']; linarith
  set E : ℝ := Real.exp (-β / a) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  -- split the exponent in half
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hexpeq : -β / a + -β / a = -β / ((M : ℝ) - 1) := by
    rw [ha', ← add_div, div_eq_div_iff (ne_of_gt (by linarith : (0:ℝ) < 2 * ((M:ℝ) - 1)))
      (ne_of_gt hM1)]
    ring
  have hhalf : Real.exp (-β / ((M : ℝ) - 1)) = E * E := by
    rw [hE, ← Real.exp_add, hexpeq]
  have hgoal : Real.exp (-(1 / (2 * ((M : ℝ) - 1))) * β) = E := by
    rw [hE, ha', show -(1 / (2 * ((M : ℝ) - 1))) * β = -β / (2 * ((M : ℝ) - 1)) by ring]
  rw [hhalf, hgoal]
  -- absorb `β E ≤ a e^{-1}`
  have hβE : β * E ≤ a * Real.exp (-1) := mul_exp_neg_div_le ha β
  have hKc : (0 : ℝ) ≤ ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hNM : (0 : ℝ) ≤ ((N ^ 2 * M : ℕ) : ℝ) := by positivity
  have hstep : (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E
      ≤ ((N ^ 2 * M : ℕ) : ℝ)
        + 8 * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1) := by
    have hexp : 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (β * E)
        ≤ 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (a * Real.exp (-1)) := by
      exact mul_le_mul_of_nonneg_left hβE (by linarith)
    rw [ha'] at hexp
    nlinarith [mul_le_mul_of_nonneg_left hE1 hNM]
  calc (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * (E * E)
      = ((((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E) * E := by
        ring
    _ ≤ (((N ^ 2 * M : ℕ) : ℝ)
        + 8 * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1)) * E :=
        mul_le_mul_of_nonneg_right hstep hE0.le
    _ ≤ (8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ)) * E :=
        mul_le_mul_of_nonneg_right (const_bounds hM hN).1 hE0.le

/-- Assumption **(17)** of Proposition 12, with `s₂ = 2β`, `δ = 1/((M+1)N)` and
`C = 8 e^{-1} (M+1)⁴ N³`.

This is where Corollary 15 enters: it turns `s₂ / c_β` into `4β N³(M+1)³ e^{-β/(M-1)}`, and
step (20) of the paper absorbs the factor `β` into half of the exponent. -/
theorem max_le_of_isCharacteristicTime (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {c : ℝ} (hc : IsCharacteristicTime (N := N) β o c) :
    max (2 * β / c) ((((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) *
        Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)))
      ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) *
          Real.exp (-(1 / (((M + 1) * N : ℕ) : ℝ)) * β) := by
  have hn : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  set Kc : ℝ := ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) with hKc
  have hKcpos : 0 < Kc := by
    rw [hKc]
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (Nat.pow_pos (Nat.succ_pos M))
  set D : ℝ := (((M + 1) * N : ℕ) : ℝ) with hD
  have hDpos : 0 < D := by
    rw [hD]; exact_mod_cast Nat.mul_pos (Nat.succ_pos M) (by omega : 0 < N)
  set a : ℝ := 2 * ((M : ℝ) - 1) with ha'
  have ha : 0 < a := by rw [ha']; linarith
  set E : ℝ := Real.exp (-β / a) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- the target exponential, and the comparison `E ≤ e^{-β/D}`
  have hrw : -(1 / D) * β = -β / D := by ring
  have hDa : a ≤ D := by
    rw [ha', hD]; push_cast; nlinarith
  have hdd : β / D ≤ β / a := div_le_div_of_nonneg_left hβ ha hDa
  have hEle : E ≤ Real.exp (-β / D) := by
    rw [hE, Real.exp_le_exp, show -β / a = -(β / a) by ring, show -β / D = -(β / D) by ring]
    linarith
  have hEle' : E ≤ Real.exp (-(1 / D) * β) := by rwa [hrw]
  refine max_le ?_ ?_
  · -- (a) the `s₂ / c` half, through Corollary 15
    have hcpos : 0 < c := hc.1
    have h15' := le_characteristicTime hM hN hβ hc
    set F : ℝ := Real.exp (β / ((M : ℝ) - 1)) with hF
    have hFpos : 0 < F := Real.exp_pos _
    have hbpos : (0 : ℝ) < 1 / 2 * Kc⁻¹ * F := by positivity
    have hdiv : 2 * β / c ≤ 2 * β / (1 / 2 * Kc⁻¹ * F) :=
      div_le_div_of_nonneg_left (by linarith) hbpos h15'
    have hfe : 2 * β / (1 / 2 * Kc⁻¹ * F) = 4 * Kc * (β * E) * E := by
      have hexpeq : -β / a + -β / a = -β / ((M : ℝ) - 1) := by
        rw [ha', ← add_div,
          div_eq_div_iff (ne_of_gt (by linarith : (0:ℝ) < 2 * ((M:ℝ) - 1))) (ne_of_gt hM1)]
        ring
      have hEE : E * E = Real.exp (-β / ((M : ℝ) - 1)) := by
        rw [hE, ← Real.exp_add, hexpeq]
      rw [show 4 * Kc * (β * E) * E = 4 * Kc * β * (E * E) by ring, hEE,
        show -β / ((M : ℝ) - 1) = -(β / ((M : ℝ) - 1)) by ring, Real.exp_neg, ← hF]
      field_simp
      ring
    calc 2 * β / c ≤ 4 * Kc * (β * E) * E := hdiv.trans_eq hfe
      _ ≤ 4 * Kc * (a * Real.exp (-1)) * E :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_exp_neg_div_le ha β) (by positivity)) hE0.le
      _ = 8 * Real.exp (-1) * Kc * ((M : ℝ) - 1) * E := by rw [ha']; ring
      _ ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) * E :=
          mul_le_mul_of_nonneg_right (const_bounds hM hN).2.1 hE0.le
      _ ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) * Real.exp (-(1 / D) * β) :=
          mul_le_mul_of_nonneg_left hEle' (by positivity)
  · -- (b) the `ε₂` half: the exponentials already agree
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (const_bounds hM hN).2.2 (Real.exp_pos _).le

/-- **Proposition 12**, the consequence for this model of Theorem 5.3 of [LM22]: under the
four assumptions (15)–(18), the rescaled exit time from a consensus set is exponential up to
an error `K' β³ e^{-min(δ/3, 1/2, θ) β}`, and the mean exit time barely depends on the
starting state.

**This is an axiom, not a theorem.**  It is not a result of arXiv:2607.19651: the paper
derives it from Theorem 5.3 of [LM22], whose proof is a metastability argument for a general
time-homogeneous strong Markov process.  Nothing inside this repository can discharge it, so
it is declared rather than left as a `sorry` that looks like the others.  Everything that
depends on it is listed separately in the CI axiom check: those results are sorry-free, and
true modulo this one citation.

It is stated for *this* process on purpose.  Stated abstractly — for an arbitrary family of
measures and an arbitrary hitting time — it would be **inconsistent**: taking the zero measure
with an empty ladder set satisfies (15)–(18) vacuously while falsifying the conclusion at
`t = 0`.  What rules that out is the strong Markov property, which is exactly the content of
[LM22] and is not expressible here.  So Theorem 31 will need its own twin for the biased
process; one axiom cannot serve both.

The hypotheses are named after the equations of the paper: `h15` is (15), `h16` is (16),
`h17` is (17) and `h18` is (18).  Unlike the paper's numbered display, `ε₁`, `ε₂`, `s₁` and
`s₂` are *functions of* `β`: the proof of Theorem 3 instantiates them at `s₂ = 2β` and
`ε₂ = (M+1)² N² e^{-β/((M+1)N)}`, and the constraint `ε₁ + ε₂ ≤ 1/2` holds, in the paper's
words, only "for `β` sufficiently big".  Binding them as constants ahead of `β`, as an earlier
version of this statement did, makes the hypotheses unsatisfiable. -/
axiom exitTime_approx_exponential (hM : 2 ≤ M) (hN : 3 ≤ N) (o : Opinion M)
    (ε₁ ε₂ s₁ s₂ : ℝ → ℝ) {C δ K θ β₁ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hK : 0 < K) (hθ : 0 < θ)
    (hpos : ∀ β : ℝ, β₁ ≤ β → 0 < ε₁ β ∧ 0 < ε₂ β ∧ 0 < s₁ β ∧ 0 < s₂ β)
    (hsum : ∀ β : ℝ, β₁ ≤ β → ε₁ β + ε₂ β ≤ 1 / 2)
    (h15 : ∀ β : ℝ, β₁ ≤ β → ∀ l : Pressure N M, IsLadder o l →
      ctsPathMeasure β l
          {ω | hittingTimeCts l (consensusSetOther N o) ω ≤ ENNReal.ofReal (s₁ β)}
        ≤ ENNReal.ofReal (ε₁ β))
    (h16 : ∀ β : ℝ, β₁ ≤ β → ∀ u : Pressure N M, IsState u →
      probHittingGT β u ({v | IsLadder o v} ∪ consensusSetOther N o)
          (ENNReal.ofReal (s₂ β))
        ≤ ENNReal.ofReal (ε₂ β))
    (h17 : ∀ β : ℝ, β₁ ≤ β → ∀ c : ℝ, IsCharacteristicTime (N := N) β o c →
      max (s₂ β / c) (ε₂ β) ≤ C * Real.exp (-δ * β))
    (h18 : ∀ β : ℝ, β₁ ≤ β → ∀ u : Pressure N M, IsConsensus o u →
      ctsPathMeasure β u
          {ω | hittingTimeCts u (consensusSetOther N o) ω ≤ ENNReal.ofReal (s₂ β)}
        ≤ ENNReal.ofReal (K * Real.exp (-θ * β))) :
    ∃ β₀ K' : ℝ, β₁ ≤ β₀ ∧ 0 < β₀ ∧ 0 < K' ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ u : Pressure N M, IsConsensus o u →
      (∀ t : ℝ, 0 ≤ t →
        |(probHittingGT β u (consensusSetOther N o)
            (ENNReal.ofReal t * expHittingTimeCts β u (consensusSetOther N o))).toReal
          - Real.exp (-t)|
        ≤ K' * β ^ 3 * Real.exp (-min (min (δ / 3) (1 / 2)) θ * β)) ∧
      ∀ v : Pressure N M, IsConsensus o v →
        |(expHittingTimeCts β u (consensusSetOther N o)).toReal /
            (expHittingTimeCts β v (consensusSetOther N o)).toReal - 1|
          ≤ K' * β ^ 3 * Real.exp (-min (min (δ / 3) (1 / 2)) θ * β)

/-- **Theorem 3 (Metastability).** There are `β₀, C₁ > 0` and `C₂ ∈ (0, 1/2)`, depending only
on `M` and `N`, such that for `β ≥ β₀`, every opinion `o` and every consensus state `u ∈ C^o`,
the rescaled exit time from `C^o` is exponential of parameter one up to `C₁ β³ e^{-C₂ β}`, and
the mean exit times from two consensus states agree to the same order.

This is Proposition 12 applied with the bounds of Lemmas 13 and 14. -/
theorem metastability (hM : 2 ≤ M) (hN : 3 ≤ N) :
    ∃ β₀ C₁ C₂ : ℝ, 0 < β₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧ C₂ < 1 / 2 ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ o : Opinion M, ∀ u : Pressure N M, IsConsensus o u →
        (∀ t : ℝ, 0 ≤ t →
          |(probHittingGT β u (consensusSetOther N o)
              (ENNReal.ofReal t * expHittingTimeCts β u (consensusSetOther N o))).toReal
            - Real.exp (-t)| ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β)) ∧
        ∀ v : Pressure N M, IsConsensus o v →
          |(expHittingTimeCts β u (consensusSetOther N o)).toReal /
              (expHittingTimeCts β v (consensusSetOther N o)).toReal - 1|
            ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β) := by
  have hn : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hKcpos : (0 : ℝ) < ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (Nat.pow_pos (Nat.succ_pos M))
  have hQpos : (0 : ℝ) < (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (Nat.succ_pos M)) (Nat.pow_pos (by omega : 0 < N))
  have hDpos : (0 : ℝ) < (((M + 1) * N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos M) (by omega : 0 < N)
  have hC4 : (0 : ℝ) < (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (Nat.succ_pos M)) (Nat.pow_pos (by omega : 0 < N))
  have hCpos : (0 : ℝ) < 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) := by positivity
  have hδpos : (0 : ℝ) < 1 / (((M + 1) * N : ℕ) : ℝ) := by positivity
  have hθpos : (0 : ℝ) < 1 / (2 * ((M : ℝ) - 1)) := by positivity
  -- the threshold above which `ε₁ + ε₂ ≤ 1/2`
  set β₁ : ℝ := max 1 (max (8 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1))
    (4 * (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * (((M + 1) * N : ℕ) : ℝ))) with hβ₁def
  have hβ₁one : (1 : ℝ) ≤ β₁ := le_max_left _ _
  have hpos' : ∀ β : ℝ, β₁ ≤ β → (0 : ℝ) < β := fun β hβ =>
    lt_of_lt_of_le zero_lt_one (le_trans hβ₁one hβ)
  have hsum : ∀ β : ℝ, β₁ ≤ β →
      2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1))
        + (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ))
      ≤ 1 / 2 := by
    intro β hβ
    have hβpos := hpos' β hβ
    have b1 : 8 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1) ≤ β :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hβ
    have b2 : 4 * (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * (((M + 1) * N : ℕ) : ℝ) ≤ β :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hβ
    have e1 : 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1))
        ≤ 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (((M : ℝ) - 1) / β) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_le hM1 hβpos) (by positivity)
    have e2 : (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ))
        ≤ (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * ((((M + 1) * N : ℕ) : ℝ) / β) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_le hDpos hβpos) (by positivity)
    have f1 : 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (((M : ℝ) - 1) / β) ≤ 1 / 4 := by
      rw [show 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (((M : ℝ) - 1) / β)
          = (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1)) / β by ring,
        div_le_iff₀ hβpos]
      linarith
    have f2 : (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * ((((M + 1) * N : ℕ) : ℝ) / β) ≤ 1 / 4 := by
      rw [show (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * ((((M + 1) * N : ℕ) : ℝ) / β)
          = ((((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * (((M + 1) * N : ℕ) : ℝ)) / β by ring,
        div_le_iff₀ hβpos]
      linarith
    linarith
  -- Proposition 12, opinion by opinion
  have key : ∀ o : Opinion M, ∃ β₀ K' : ℝ, β₁ ≤ β₀ ∧ 0 < β₀ ∧ 0 < K' ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ u : Pressure N M, IsConsensus o u →
      (∀ t : ℝ, 0 ≤ t →
        |(probHittingGT β u (consensusSetOther N o)
            (ENNReal.ofReal t * expHittingTimeCts β u (consensusSetOther N o))).toReal
          - Real.exp (-t)|
        ≤ K' * β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
            (1 / (2 * ((M : ℝ) - 1))) * β)) ∧
      ∀ v : Pressure N M, IsConsensus o v →
        |(expHittingTimeCts β u (consensusSetOther N o)).toReal /
            (expHittingTimeCts β v (consensusSetOther N o)).toReal - 1|
          ≤ K' * β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
              (1 / (2 * ((M : ℝ) - 1))) * β) := by
    intro o
    exact exitTime_approx_exponential hM hN o
      (fun β => 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1)))
      (fun β => (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)))
      (fun _ => 1) (fun β => 2 * β)
      hCpos hδpos hCpos hθpos
      (fun β hβ => ⟨by positivity, by positivity, one_pos, by linarith [hpos' β hβ]⟩)
      hsum
      (fun β hβ l hl => measure_hittingTime_le_one hM hN (hpos' β hβ).le hl)
      (fun β hβ u hu => probHittingGT_ladderOther_le hM hN (hpos' β hβ).le o hu)
      (fun β hβ c hc => max_le_of_isCharacteristicTime hM hN (hpos' β hβ).le hc)
      (fun β hβ u hu => measure_hittingTime_le_two_mul hM hN (hpos' β hβ) hu)
  choose b k hbβ₁ hbpos hkpos hmain using key
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ o : Opinion M, b o ≤ B := Finite.exists_le b
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, ∀ o : Opinion M, k o ≤ Kb := Finite.exists_le k
  refine ⟨max B 1, max Kb 1, min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
    (1 / (2 * ((M : ℝ) - 1))), lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), lt_min (lt_min (by positivity) (by norm_num))
    hθpos, ?_, ?_⟩
  · -- `C₂ < 1/2`, because `δ/3 = 1/(3(M+1)N) ≤ 1/27`
    refine lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) ?_
    have hD9 : (9 : ℝ) ≤ (((M + 1) * N : ℕ) : ℝ) := by push_cast; nlinarith
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3), one_div]
    rw [inv_lt_iff_one_lt_mul₀ hDpos]
    nlinarith
  · intro β hβ o u hu
    have hbβ : b o ≤ β := le_trans (hB o) (le_trans (le_max_left _ _) hβ)
    obtain ⟨h1, h2⟩ := hmain o β hbβ u hu
    have hfac : (0 : ℝ) ≤ β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3)
        (1 / 2)) (1 / (2 * ((M : ℝ) - 1))) * β) := by
      have : (0 : ℝ) < β := lt_of_lt_of_le (lt_of_lt_of_le (hbpos o) (le_refl _)) hbβ
      positivity
    have hup : k o * β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
          (1 / (2 * ((M : ℝ) - 1))) * β)
        ≤ max Kb 1 * β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
          (1 / (2 * ((M : ℝ) - 1))) * β) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_trans (hKb o) (le_max_left _ _)) hfac
    exact ⟨fun t ht => le_trans (h1 t ht) hup, fun v hv => le_trans (h2 v hv) hup⟩

end Theorem3

end SocialNetwork
