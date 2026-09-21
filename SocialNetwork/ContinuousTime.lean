/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Appendix
import SocialNetwork.Clocks
import SocialNetwork.Minorisation
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
which needs a Doeblin minorisation), the concentration of that measure (Theorem 2.1) and the
metastability estimate (Theorem 3).  Those carry a `sorry`.  See `blueprint/blueprint.md`.

Theorem 2.2 is **proved**, and so is the display inside its proof.  It says nothing about the
invariant measure — it is a statement about the process started at a fixed `u` — so Doeblin
never enters, and what it needs instead is the analysis of the clock in
`### The holding times, and the greedy event in continuous time` below: conditionally on the
past, each holding time is exponential of rate `q_β` at the matrix the history reaches, a
greedy run never sits at the zero matrix where that rate is small, and Proposition 8
transports from the skeleton to this sample space.  Both inherit `sorryAx` from Proposition 7,
and so from Lemmas 19 and 20, and from nothing else.

That is why this file imports `SocialNetwork.Appendix`, where Proposition 7 lives, rather than
the other way round: `Appendix` used to import this file and never used anything from it.

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
* `SocialNetwork.tendsto_hittingTime_ladderSet` — **Theorem 2.2**, proved from the display
  below, modulo Proposition 7.
* `SocialNetwork.probHittingGT_ladderSet_le_of_ne_zero` — the display inside the proof of
  Theorem 2.2, proved modulo Proposition 7.
* `SocialNetwork.zeta_pow_le_ctsPathMeasure_greedyEvents` — **Proposition 8** on this sample
  space, proved.
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

/-- At the zero matrix every rate equals `1`, so the total rate is `MN` and the first
expression takes an exponential time of mean `1/(MN)`.

This is the constant Corollary 11 and equation (19) are stated with, and it is the reason the
zero matrix has to be excluded from part 2 of Theorem 2: everywhere else on `S` some entry is
at least `1`, so the total rate is at least `e^{β/(M-1)}`. -/
@[simp]
theorem totalRate_zero (β : ℝ) : totalRate β (0 : Pressure N M) = ((M * N : ℕ) : ℝ) := by
  have h : ∀ p : Jump N M, jumpRate β (0 : Pressure N M) p.1 p.2 = 1 := by
    intro p; simp [jumpRate]
  rw [totalRate, Finset.sum_congr rfl fun p _ => h p]
  simp [Finset.card_univ, Fintype.card_prod, Nat.mul_comm]

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

/-! #### One step, read off the clocks

`stepLaw` is the *jump-hold* form of one step.  The proof of Theorem 1.1 at p. 16 needs the
*clock* form — one exponential clock per pair, at the rate of that pair, the first to ring
winning — because its equation (11) is a statement about the clocks of a sub-family: the
expressions coming from actors carrying pressure below `N` have total rate at most `NMe^{βN}`
whatever the rest of the matrix does, and that is what sandwiches them between two Poisson
processes.  The two forms are the same law, which is `SocialNetwork.Clocks`. -/

/-- **A winner can be chosen measurably.**  Ties are null but not impossible, so the choice
has to be made; the order used to break them is an implementation detail, and
`SocialNetwork.pi_expMeasure_race_Ioi` holds for every measurable choice. -/
theorem exists_isWinner_jump :
    ∃ w : (Jump N M → ℝ) → Jump N M, IsWinner w := by
  let _ : LinearOrder (Jump N M) :=
    LinearOrder.lift' (toLex : Jump N M → Actor N ×ₗ Opinion M) fun _ _ h => h
  exact ⟨firstClock, isWinner_firstClock⟩

/-- **One step is the race between the clocks.**  On the rectangles that determine the law —
the pair is `p`, and it is expressed after time `t` — the jump-hold form of `stepLaw` and the
clock form agree. -/
theorem stepLaw_prod_Ioi (β : ℝ) (v : Pressure N M) {w : (Jump N M → ℝ) → Jump N M}
    (hw : IsWinner w) (p : Jump N M) {t : ℝ} (ht : 0 ≤ t) :
    stepLaw β v (({p} : Set (Jump N M)) ×ˢ Set.Ioi t)
      = Measure.pi (fun q : Jump N M => expMeasure (jumpRate β v q.1 q.2))
          {c | w c = p ∧ c (w c) ∈ Set.Ioi t} := by
  have hrate : ∀ q : Jump N M, 0 < jumpRate β v q.1 q.2 := fun q => jumpRate_pos β v q.1 q.2
  have hpos : 0 < totalRate β v := totalRate_pos β v
  have : IsProbabilityMeasure (expMeasure (totalRate β v)) :=
    isProbabilityMeasure_expMeasure hpos
  rw [pi_expMeasure_race_Ioi hrate hw p ht]
  have htot : ∑ q : Jump N M, jumpRate β v q.1 q.2 = totalRate β v := rfl
  rw [htot, stepLaw, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p)]
  congr 1
  -- the Gibbs law of equation (3) is the normalised rate
  have hsum : ∑' q : Jump N M, jumpWeight β v q = ENNReal.ofReal (totalRate β v) := by
    rw [tsum_fintype, totalRate]
    exact (ENNReal.ofReal_sum_of_nonneg fun q _ => (hrate q).le).symm
  rw [jumpPMF_apply, hsum, jumpWeight, ← div_eq_mul_inv,
    ← ENNReal.ofReal_div_of_pos hpos]

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
  simp only [jumpCount]
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
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, jumpCount_eq_iff t ω hk]
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
        Set.mem_ofPred_eq, not_exists]
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

/-! ### Reducing a hitting time to a countable infimum

The infimum defining a hitting time runs over the uncountable family `{t : 0 ≤ t}`.  Reducing
it to a countable one does **not** need right-continuity of `t ↦ U_t (ω)`, which would hold
only almost surely.  It is enough that the process factors through `jumpCount ω ·`, together
with two facts about that function, both of which hold for every `ω`.

Write `S (t) = {n : Tₙ ≤ t}`, so that `jumpCount ω t = sSup S (t)`.

* Where `S (t)` is bounded, `k = jumpCount ω t` lies in `S (t)` and bounds it, so
  `max (T_k, 0) ≤ t` is a time at which the jump count is again `k`.  The infimum over that
  level set is therefore attained, at a time named by `k` alone.
* Where `S (t)` is unbounded — the explosion event, on which `sSup` returns its junk value
  `0` — every larger time has `S` unbounded too, so the junk value persists to the right and
  the rationals above `t` do just as well.

So the times `max (T_k, 0)` and the non-negative rationals already meet the infimum, and they
are countably many.  **No counterpart in the paper**, which does not address measurability.
-/

section Hitting

variable {α : Type*}

/-- `max (T_k, 0)` has jump count exactly `k`, whenever no jump time beyond the `k`-th has
occurred by then.

**No counterpart in the paper.**  Unlike `SocialNetwork.jumpCount_eq_iff` this needs no
`k ≠ 0`: the hypothesis rules out the unbounded case by hand, so the junk value of `sSup`
cannot interfere. -/
theorem jumpCount_max_jumpTime (ω : ℕ → Step N M) (k : ℕ)
    (h : ∀ m : ℕ, jumpTime m ω ≤ max (jumpTime k ω) 0 → m ≤ k) :
    jumpCount ω (max (jumpTime k ω) 0) = k := by
  have hk : jumpTime k ω ≤ max (jumpTime k ω) 0 := le_max_left _ _
  have hub : ∀ m ∈ {n : ℕ | jumpTime n ω ≤ max (jumpTime k ω) 0}, m ≤ k := fun m hm => h m hm
  exact le_antisymm (csSup_le ⟨k, hk⟩ hub) (le_csSup ⟨k, hub⟩ hk)

/-- Below the explosion time the infimum of a level set of `jumpCount` is attained, at
`max (T_k, 0)`.

**No counterpart in the paper.** -/
theorem max_jumpTime_jumpCount_le (ω : ℕ → Step N M) {t : ℝ} (ht : 0 ≤ t)
    (hb : BddAbove {n : ℕ | jumpTime n ω ≤ t}) :
    max (jumpTime (jumpCount ω t) ω) 0 ≤ t ∧
      ∀ m : ℕ, jumpTime m ω ≤ max (jumpTime (jumpCount ω t) ω) 0 → m ≤ jumpCount ω t := by
  have hne : {n : ℕ | jumpTime n ω ≤ t}.Nonempty := ⟨0, by simpa using ht⟩
  have hmem : jumpTime (jumpCount ω t) ω ≤ t := Nat.sSup_mem hne hb
  refine ⟨max_le hmem ht, fun m hm => le_csSup hb ?_⟩
  exact le_trans hm (max_le hmem ht)

/-- The explosion event is closed upwards, so the junk value of `jumpCount` persists to the
right of any time at which it is returned.

**No counterpart in the paper.** -/
theorem jumpCount_eq_of_not_bddAbove (ω : ℕ → Step N M) {t t' : ℝ} (htt : t ≤ t')
    (h : ¬ BddAbove {n : ℕ | jumpTime n ω ≤ t}) :
    jumpCount ω t' = jumpCount ω t := by
  have h' : ¬ BddAbove {n : ℕ | jumpTime n ω ≤ t'} := fun hb =>
    h (hb.mono fun n hn => le_trans hn htt)
  rw [jumpCount, jumpCount, Nat.sSup_of_not_bddAbove h, Nat.sSup_of_not_bddAbove h']

open Classical in
/-- The countable family of times that meets the infimum: the jump times pushed up to `0`,
and the non-negative rationals.

**No counterpart in the paper.** -/
noncomputable def hittingCandidates (F : ℕ → (ℕ → Step N M) → α) (θ : Set α)
    (ω : ℕ → Step N M) : ℝ≥0∞ :=
  (⨅ k : ℕ, if (∀ m : ℕ, jumpTime m ω ≤ max (jumpTime k ω) 0 → m ≤ k) ∧ F k ω ∈ θ then
      ENNReal.ofReal (max (jumpTime k ω) 0) else ⊤) ⊓
    ⨅ q : ℚ, if F (jumpCount ω (max (q : ℝ) 0)) ω ∈ θ then
      ENNReal.ofReal (max (q : ℝ) 0) else ⊤

/-- The infimum over `t ≥ 0` is the infimum over the countable family.

**No counterpart in the paper**; this is the whole content of the measurability of the
hitting times. -/
theorem sInf_image_eq_hittingCandidates (F : ℕ → (ℕ → Step N M) → α) (θ : Set α)
    (ω : ℕ → Step N M) :
    sInf ((fun t : ℝ => ENNReal.ofReal t) ''
        {t : ℝ | 0 ≤ t ∧ F (jumpCount ω t) ω ∈ θ})
      = hittingCandidates F θ ω := by
  classical
  set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ F (jumpCount ω t) ω ∈ θ} with hA
  refine le_antisymm ?_ ?_
  · -- Every candidate is either `⊤` or `ofReal` of a time in `A`.
    refine le_inf (le_iInf fun k => ?_) (le_iInf fun q => ?_)
    · split_ifs with hk
      · refine sInf_le ⟨max (jumpTime k ω) 0, ⟨le_max_right _ _, ?_⟩, rfl⟩
        rw [jumpCount_max_jumpTime ω k hk.1]
        exact hk.2
      · exact le_top
    · split_ifs with hq
      · exact sInf_le ⟨max (q : ℝ) 0, ⟨le_max_right _ _, hq⟩, rfl⟩
      · exact le_top
  · -- Every time in `A` is met by a candidate, exactly below the explosion time and from
    -- above by rationals on it.
    refine le_sInf ?_
    rintro x ⟨t, ⟨ht0, htθ⟩, rfl⟩
    by_cases hb : BddAbove {n : ℕ | jumpTime n ω ≤ t}
    · obtain ⟨hle, hub⟩ := max_jumpTime_jumpCount_le ω ht0 hb
      refine le_trans inf_le_left (le_trans (iInf_le _ (jumpCount ω t)) ?_)
      rw [if_pos ⟨hub, htθ⟩]
      exact ENNReal.ofReal_le_ofReal hle
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have hεpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right t hεpos)
      have hq0 : max (q : ℝ) 0 = (q : ℝ) := max_eq_left (le_trans ht0 hq1.le)
      have hcount : jumpCount ω (max (q : ℝ) 0) = jumpCount ω t := by
        rw [hq0]; exact jumpCount_eq_of_not_bddAbove ω hq1.le hb
      refine le_trans inf_le_right (le_trans (iInf_le _ q) ?_)
      rw [if_pos (by rw [hcount]; exact htθ), hq0]
      calc ENNReal.ofReal (q : ℝ) ≤ ENNReal.ofReal (t + (ε : ℝ)) :=
            ENNReal.ofReal_le_ofReal hq2.le
        _ = ENNReal.ofReal t + ε := by
            rw [ENNReal.ofReal_add ht0 ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- Each candidate is a measurable function of the realisation, so the infimum is one too.

**No counterpart in the paper.** -/
theorem measurable_hittingCandidates [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {F : ℕ → (ℕ → Step N M) → α} (hF : ∀ k, Measurable (F k))
    (θ : Set α) :
    Measurable (hittingCandidates F θ) := by
  classical
  have hθ : MeasurableSet θ := (Set.to_countable θ).measurableSet
  have hjump : ∀ t : ℝ, Measurable fun ω : ℕ → Step N M => F (jumpCount ω t) ω := by
    intro t
    have h : (fun ω : ℕ → Step N M => F (jumpCount ω t) ω)
        = (fun p : ℕ × (ℕ → Step N M) => F p.1 p.2) ∘ fun ω : ℕ → Step N M => (jumpCount ω t, ω) :=
      rfl
    rw [h]
    exact (measurable_from_prod_countable_right fun k => hF k).comp
      ((measurable_jumpCount t).prodMk measurable_id)
  refine Measurable.inf (Measurable.iInf fun k => ?_) (Measurable.iInf fun q => ?_)
  · have hset : MeasurableSet
        {ω : ℕ → Step N M |
          (∀ m : ℕ, jumpTime m ω ≤ max (jumpTime k ω) 0 → m ≤ k) ∧ F k ω ∈ θ} := by
      have h1 : MeasurableSet
          {ω : ℕ → Step N M | ∀ m : ℕ, jumpTime m ω ≤ max (jumpTime k ω) 0 → m ≤ k} := by
        have : {ω : ℕ → Step N M | ∀ m : ℕ, jumpTime m ω ≤ max (jumpTime k ω) 0 → m ≤ k}
            = ⋂ m : ℕ, {ω : ℕ → Step N M | m ≤ k ∨ max (jumpTime k ω) 0 < jumpTime m ω} := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_iInter]
          constructor
          · exact fun h m => (le_or_gt (jumpTime m ω) (max (jumpTime k ω) 0)).imp (h m) id
          · intro h m hm
            rcases h m with h | h
            · exact h
            · exact absurd hm (not_le.2 h)
        rw [this]
        refine MeasurableSet.iInter fun m => ?_
        rcases le_or_gt m k with hm | hm
        · simp [hm]
        · have : {ω : ℕ → Step N M | m ≤ k ∨ max (jumpTime k ω) 0 < jumpTime m ω}
              = {ω | max (jumpTime k ω) 0 < jumpTime m ω} := by
            ext ω; simp [Nat.not_le.2 hm]
          rw [this]
          exact measurableSet_lt ((measurable_jumpTime k).max measurable_const)
            (measurable_jumpTime m)
      exact h1.inter (hF k hθ)
    exact Measurable.ite hset
      (ENNReal.measurable_ofReal.comp ((measurable_jumpTime k).max measurable_const))
      measurable_const
  · exact Measurable.ite (hjump (max (q : ℝ) 0) hθ) measurable_const measurable_const

end Hitting

/-- The hitting time `R^{β,u} (θ) = inf {t ≥ 0 : U_t^{β,u} ∈ θ}` of the paper, valued in
`ℝ≥0∞` so that `⊤` records that `θ` is never reached. -/
noncomputable def hittingTimeCts (u : Pressure N M) (θ : Set (Pressure N M))
    (ω : ℕ → Step N M) : ℝ≥0∞ :=
  sInf ((fun t : ℝ => ENNReal.ofReal t) '' {t : ℝ | 0 ≤ t ∧ process u t ω ∈ θ})

/-- The hitting time is a measurable function of the realisation.

**No counterpart in the paper**, which does not address measurability.

An earlier note here claimed this needed an almost-sure formulation, on the grounds that
reducing the infimum over `{t : 0 ≤ t}` to a countable one needs `t ↦ U_t (ω)` to be
right-continuous, which holds only where the holding times are positive.  **That was wrong**:
right-continuity is one route to the reduction, not the only one, and the reduction holds for
every `ω` — see `SocialNetwork.sInf_image_eq_hittingCandidates`.  What it uses instead is
that the level sets of `jumpCount ω ·` are met by two countable families of times: below the
explosion time the infimum of a level set is *attained*, at `max (T_k, 0)`, and on the
explosion event the junk value of `sSup` persists to the right, so the rationals above a time
serve in its place.  Neither needs the holding times to be positive. -/
theorem measurable_hittingTimeCts (u : Pressure N M) (θ : Set (Pressure N M)) :
    Measurable (hittingTimeCts (N := N) (M := M) u θ) := by
  have h : hittingTimeCts (N := N) (M := M) u θ
      = hittingCandidates (fun k ω => (Trajectory.ofStepPath ω).state u k) θ :=
    funext fun ω =>
      sInf_image_eq_hittingCandidates (fun k ω => (Trajectory.ofStepPath ω).state u k) θ ω
  rw [h]
  exact measurable_hittingCandidates (fun k => measurable_state_ofStepPath u k) θ

variable [NeZero N] [NeZero M]

/-- The law of the hitting time `R^{β,u} (θ)`, as a number: the probability, under the process
started at `u`, that `θ` has not been reached by time `t`. -/
noncomputable def probHittingGT (β : ℝ) (u : Pressure N M) (θ : Set (Pressure N M))
    (t : ℝ≥0∞) : ℝ≥0∞ :=
  ctsPathMeasure β u {ω | t < hittingTimeCts u θ ω}

/-- `P (R^{β,u} (θ) > T₁ + t)`: the hitting time of `θ` exceeds the first jump time by more
than `t`.

This is the shape Corollary 11 is stated in.  Writing the waiting time as the process's own
`T₁` rather than as a separate random variable is what makes `τ` exponential of mean `1/(MN)`
from `0` — `totalRate_zero` — and independent of the process that follows it, which is what
the corollary asserts of it. -/
noncomputable def probHittingGTAfterFirstJump (β : ℝ) (u : Pressure N M)
    (θ : Set (Pressure N M)) (t : ℝ) : ℝ≥0∞ :=
  ctsPathMeasure β u {ω | ENNReal.ofReal (jumpTime 1 ω + t) < hittingTimeCts u θ ω}

/-- `P (R^{β,u} (L^o) < min {t, R^{β,u} (C^{-o})})`: a ladder supporting `o` is reached before
time `t`, and before the process reaches a consensus for any other opinion.

This is the quantity of Remark 6.  It is not `SocialNetwork.probHittingGT` of anything: the
event compares two hitting times of the same realisation. -/
noncomputable def probHittingLadderFirst (β : ℝ) (o : Opinion M) (u : Pressure N M)
    (t : ℝ≥0∞) : ℝ≥0∞ :=
  ctsPathMeasure β u {ω | hittingTimeCts u {v : Pressure N M | IsLadder o v} ω
    < min t (hittingTimeCts u (consensusSetOther N o) ω)}

omit [NeZero N] [NeZero M] in
theorem measurableSet_hittingLadderFirst (o : Opinion M) (u : Pressure N M) (t : ℝ≥0∞) :
    MeasurableSet {ω : ℕ → Step N M |
      hittingTimeCts u {v : Pressure N M | IsLadder o v} ω
        < min t (hittingTimeCts u (consensusSetOther N o) ω)} :=
  measurableSet_lt (measurable_hittingTimeCts _ _)
    (measurable_const.min (measurable_hittingTimeCts _ _))

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

**Proved**, and it is the Doeblin step: `SocialNetwork.minorisation_iterateKernel` is the
minorisation at p. 17 of the paper, and
`SocialNetwork.existsUnique_invariant_of_iterate_minorisation` turns it into existence *and*
uniqueness.  Neither half needs irreducibility, aperiodicity, or a recurrence theory; the
existence half is the excursion measure, which the minorisation makes summable.

The paper's `N ≥ 3` is not used: a non-empty network is enough, since the descending sweep
behind the minorisation reaches the canonical ladder for every `N ≥ 1`. -/
theorem existsUnique_invariantSkeleton (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) :
    ∃! μ : Measure (Pressure N M),
      IsProbabilityMeasure μ ∧ IsCarriedByState μ ∧ Kernel.Invariant (skeletonKernel β) μ :=
  existsUnique_invariant_skeletonKernel hM hβ

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

/-! ### The holding times, and the greedy event in continuous time

Everything Theorem 2 needs about the clock.  Three facts, and they are all the jump-hold
representation says: conditionally on the first `n + 1` steps, the holding time that follows
is exponential of rate `q_β` at the matrix the history reaches; a greedy run keeps the process
off the zero matrix, where that rate is at least `e^{β/(M-1)}`; and Proposition 8 transports
from the skeleton to this sample space, since the pairs are the first marginal of a step.

The iteration is the one of `SocialNetwork.Greedy`, along the finite-horizon kernels of the
Ionescu-Tulcea construction, carried out here for `SocialNetwork.ctsDrivingKernel` instead of
`SocialNetwork.drivingKernel`. -/

section HoldingTimes

/-! ### The tail of an exponential holding time

These live in `SocialNetwork.Clocks`, where the race between the clocks needs them too. -/

/-! ### The law of one holding time -/

variable {N M : ℕ} [NeZero N] [NeZero M] {β : ℝ} {u : Pressure N M}

/-- The law of the first `n + 1` steps. -/
noncomputable def ctsHistoryMeasure (β : ℝ) (u : Pressure N M) (n : ℕ) :
    Measure ((i : Finset.Iic n) → Step N M) :=
  Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0 n ∘ₘ
    ((stepLaw β u).map toStepHistoryZero)

instance isProbabilityMeasure_ctsHistoryMeasure (β : ℝ) (u : Pressure N M) (n : ℕ) :
    IsProbabilityMeasure (ctsHistoryMeasure β u n) := by
  rw [ctsHistoryMeasure]
  have : IsProbabilityMeasure ((stepLaw β u).map (toStepHistoryZero (N := N) (M := M))) :=
    Measure.isProbabilityMeasure_map measurable_toStepHistoryZero.aemeasurable
  infer_instance

theorem ctsPathMeasure_map_frestrictLe (β : ℝ) (u : Pressure N M) (n : ℕ) :
    (ctsPathMeasure β u).map (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n)
      = ctsHistoryMeasure β u n := by
  unfold ctsHistoryMeasure ctsPathMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe n), Kernel.traj_map_frestrictLe]

/-- The second marginal of one step is the exponential holding law. -/
theorem stepLaw_preimage_snd (β : ℝ) (v : Pressure N M) (A : Set ℝ) :
    stepLaw β v ((fun z : Step N M => z.2) ⁻¹' A) = expMeasure (totalRate β v) A := by
  have hp : IsProbabilityMeasure (expMeasure (totalRate β v)) :=
    isProbabilityMeasure_expMeasure (totalRate_pos β v)
  have hset : (fun z : Step N M => z.2) ⁻¹' A = (Set.univ : Set (Jump N M)) ×ˢ A := by
    ext z; simp
  rw [stepLaw, hset, Measure.prod_prod, measure_univ, one_mul]

/-- The first marginal of one step is the Gibbs law of equation (3). -/
theorem stepLaw_preimage_fst (β : ℝ) (v : Pressure N M) (B : Set (Jump N M)) :
    stepLaw β v ((fun z : Step N M => z.1) ⁻¹' B) = (jumpPMF β v).toMeasure B := by
  have hp : IsProbabilityMeasure (expMeasure (totalRate β v)) :=
    isProbabilityMeasure_expMeasure (totalRate_pos β v)
  have hset : (fun z : Step N M => z.1) ⁻¹' B = B ×ˢ (Set.univ : Set ℝ) := by
    ext z; simp
  rw [stepLaw, hset, Measure.prod_prod, measure_univ, mul_one]

/-! ### The greedy event on step histories -/

/-- The greedy event `⋂_{j=1}^{n+1} ξⱼ^u`, read on histories of the first `n + 1` steps. -/
def ctsGreedyHistory (u : Pressure N M) (n : ℕ) : Set ((i : Finset.Iic n) → Step N M) :=
  {h | ∀ k ≤ n, IsGreedyAt (Trajectory.ofStepHistory h) u k}

omit [NeZero N] [NeZero M] in
theorem measurableSet_ctsGreedyHistory (u : Pressure N M) (n : ℕ) :
    MeasurableSet (ctsGreedyHistory u n) := by
  have : ctsGreedyHistory u n
      = (fun h : (i : Finset.Iic n) → Step N M => fun i => (h i).1) ⁻¹' greedyHistory u n := rfl
  rw [this]
  exact (measurable_stepHistoryJumps n) (measurableSet_greedyHistory u n)

/-- The greedy event on step realisations. -/
def ctsGreedyEvents (u : Pressure N M) (n : ℕ) : Set (ℕ → Step N M) :=
  {ω | ∀ k < n, IsGreedyAt (Trajectory.ofStepPath ω) u k}

omit [NeZero N] [NeZero M] in
theorem ctsGreedyEvents_eq_preimage (u : Pressure N M) (n : ℕ) :
    ctsGreedyEvents u (n + 1)
      = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' ctsGreedyHistory u n := by
  have h1 : ctsGreedyEvents u (n + 1)
      = (fun ω : ℕ → Step N M => fun k => (ω k).1) ⁻¹' greedyEvents u (n + 1) := rfl
  have h2 : Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' ctsGreedyHistory u n
      = (fun ω : ℕ → Step N M => fun k => (ω k).1) ⁻¹'
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹' greedyHistory u n) := rfl
  rw [h1, h2, greedyEvents_eq_preimage]

/-! ### The induction step, on the step kernels -/

theorem mem_ctsGreedyHistory_succ {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Step N M}
    {h : (i : Finset.Iic n) → Step N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.le_succ n) x = h)
    (hh : h ∈ ctsGreedyHistory u n)
    (hlast : (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1
      ∈ argmaxFinset ((Trajectory.ofStepHistory h).state u (n + 1))) :
    x ∈ ctsGreedyHistory u (n + 1) := by
  refine mem_greedyHistory_succ (x := fun i => (x i).1) (h := fun i => (h i).1) ?_ hh hlast
  funext i
  exact congrArg (fun y : (i : Finset.Iic n) → Step N M => (y i).1) hx

theorem zeta_le_ctsPartialTraj_succ (hM : 2 ≤ M) (hβ : 0 ≤ β) (n : ℕ)
    {h : (i : Finset.Iic n) → Step N M} (hh : h ∈ ctsGreedyHistory u n) :
    ENNReal.ofReal (zeta N M β)
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) n (n + 1) h
          (ctsGreedyHistory u (n + 1)) := by
  set κ := Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) n (n + 1)
    with hκ
  -- the past is almost surely `h`
  have hmapA : (κ h).map
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.le_succ n)) = Measure.dirac h := by
    rw [hκ, Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Step N M) h
      (Nat.le_succ n), Kernel.partialTraj_self, Kernel.id_apply]
  have hmeasA : MeasurableSet (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M)
      (Nat.le_succ n) ⁻¹' {h}) :=
    (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Step N M) (Nat.le_succ n))
      (measurableSet_singleton h)
  have hAone : κ h (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M)
      (Nat.le_succ n) ⁻¹' {h}) = 1 := by
    have hm := Measure.map_apply (μ := κ h)
      (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Step N M) (Nat.le_succ n))
      (measurableSet_singleton h)
    rw [hmapA] at hm
    rw [← hm]
    exact Measure.dirac_apply_of_mem rfl
  have hAcompl : κ h (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M)
      (Nat.le_succ n) ⁻¹' {h})ᶜ = 0 := (prob_compl_eq_zero_iff hmeasA).2 hAone
  -- the last coordinate follows the law of one step at the matrix `h` reaches
  have hlastmeas : Measurable fun x : (i : Finset.Iic (n + 1)) → Step N M =>
      x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := measurable_pi_apply _
  have hmapB : (κ h).map (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
      x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) = ctsDrivingKernel β u n h := by
    rw [hκ, ← Kernel.map_apply _ hlastmeas, Kernel.map_partialTraj_succ_self]
  have hB : ENNReal.ofReal (zeta N M β)
      ≤ κ h ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
          (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1) ⁻¹'
        (argmaxFinset ((Trajectory.ofStepHistory h).state u (n + 1)))) := by
    have hset : (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
          (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1) ⁻¹'
        (argmaxFinset ((Trajectory.ofStepHistory h).state u (n + 1)) : Set (Jump N M))
        = (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
            x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
          ((fun z : Step N M => z.1) ⁻¹'
            (argmaxFinset ((Trajectory.ofStepHistory h).state u (n + 1)) : Set (Jump N M))) := rfl
    rw [hset, ← Measure.map_apply hlastmeas (measurable_fst MeasurableSet.of_discrete), hmapB,
      ctsDrivingKernel_apply, stepLaw_preimage_fst]
    exact zeta_le_jumpPMF_argmaxFinset hM hβ _
  exact le_measure_of_inter hAcompl hB fun x hx => mem_ctsGreedyHistory_succ hx.1 hh hx.2

/-! ### Proposition 8 on the step realisations -/

theorem zeta_le_ctsHistoryMeasure_zero (hM : 2 ≤ M) (hβ : 0 ≤ β) :
    ENNReal.ofReal (zeta N M β) ≤ ctsHistoryMeasure β u 0 (ctsGreedyHistory u 0) := by
  have hpre : toStepHistoryZero ⁻¹' ctsGreedyHistory u 0
      = (fun z : Step N M => z.1) ⁻¹' (argmaxFinset u : Set (Jump N M)) := by
    ext z
    have hact : (Trajectory.ofStepHistory (toStepHistoryZero z)).actor 0 = z.1.1 :=
      Trajectory.ofHistory_actor _ (le_refl 0)
    have hopi : (Trajectory.ofStepHistory (toStepHistoryZero z)).opinion 0 = z.1.2 :=
      Trajectory.ofHistory_opinion _ (le_refl 0)
    constructor
    · intro hz
      have h0 := (isGreedyAt_iff_entrySup
        (Trajectory.ofStepHistory (toStepHistoryZero z)) u 0).1 (hz 0 le_rfl)
      rw [Trajectory.state_zero, hact, hopi] at h0
      exact mem_argmaxFinset.2 h0
    · intro hz k hk
      have hk0 : k = 0 := Nat.le_zero.1 hk
      subst hk0
      rw [isGreedyAt_iff_entrySup, Trajectory.state_zero, hact, hopi]
      exact mem_argmaxFinset.1 hz
  unfold ctsHistoryMeasure
  rw [Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_apply measurable_toStepHistoryZero (measurableSet_ctsGreedyHistory u 0), hpre,
    stepLaw_preimage_fst]
  exact zeta_le_jumpPMF_argmaxFinset hM hβ u

theorem zeta_pow_le_ctsHistoryMeasure (hM : 2 ≤ M) (hβ : 0 ≤ β) (n : ℕ) :
    ENNReal.ofReal (zeta N M β) ^ (n + 1) ≤ ctsHistoryMeasure β u n (ctsGreedyHistory u n) := by
  induction n with
  | zero => simpa using zeta_le_ctsHistoryMeasure_zero hM hβ
  | succ n ih =>
      have hstep : ctsHistoryMeasure β u (n + 1) (ctsGreedyHistory u (n + 1))
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
              (ctsDrivingKernel β u) n (n + 1) h (ctsGreedyHistory u (n + 1))
              ∂(ctsHistoryMeasure β u n) := by
        unfold ctsHistoryMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply (measurableSet_ctsGreedyHistory u (n + 1)) (Kernel.aemeasurable _)]
      rw [hstep]
      calc ENNReal.ofReal (zeta N M β) ^ (n + 1 + 1)
          = ENNReal.ofReal (zeta N M β) * ENNReal.ofReal (zeta N M β) ^ (n + 1) := by ring
        _ ≤ ENNReal.ofReal (zeta N M β) * ctsHistoryMeasure β u n (ctsGreedyHistory u n) := by
            gcongr
        _ = ∫⁻ h, (ctsGreedyHistory u n).indicator
              (fun _ => ENNReal.ofReal (zeta N M β)) h ∂(ctsHistoryMeasure β u n) := by
            rw [lintegral_indicator (measurableSet_ctsGreedyHistory u n), setLIntegral_const]
        _ ≤ ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
              (ctsDrivingKernel β u) n (n + 1) h (ctsGreedyHistory u (n + 1))
              ∂(ctsHistoryMeasure β u n) := by
            refine lintegral_mono fun h => ?_
            by_cases hh : h ∈ ctsGreedyHistory u n
            · rw [Set.indicator_of_mem hh]
              exact zeta_le_ctsPartialTraj_succ hM hβ n hh
            · rw [Set.indicator_of_notMem hh]
              exact zero_le

/-- **Proposition 8**, read on the sample space of the continuous-time process. -/
theorem zeta_pow_le_ctsPathMeasure_greedyEvents (hM : 2 ≤ M) (hβ : 0 ≤ β) (m : ℕ) :
    ENNReal.ofReal (zeta N M β) ^ m ≤ ctsPathMeasure β u (ctsGreedyEvents u m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have huniv : ctsGreedyEvents u 0 = Set.univ := by
      ext ω; simp [ctsGreedyEvents]
    rw [pow_zero, huniv, measure_univ]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [ctsGreedyEvents_eq_preimage, ← Measure.map_apply (Preorder.measurable_frestrictLe n)
      (measurableSet_ctsGreedyHistory u n), ctsPathMeasure_map_frestrictLe]
    exact zeta_pow_le_ctsHistoryMeasure hM hβ n

/-! ### The law of one holding time -/

/-- Under one step of the kernel, the past is almost surely the history it started from. -/
theorem ctsPartialTraj_frestrictLe₂_apply (β : ℝ) (u : Pressure N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Step N M) {T : Set ((i : Finset.Iic n) → Step N M)}
    (hT : MeasurableSet T) :
    Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) n (n + 1) h
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.le_succ n) ⁻¹' T)
      = Measure.dirac h T := by
  rw [← Measure.map_apply (Preorder.measurable_frestrictLe₂
      (X := fun _ : ℕ => Step N M) (Nat.le_succ n)) hT,
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Step N M) h (Nat.le_succ n),
    Kernel.partialTraj_self, Kernel.id_apply]

/-- Under one step of the kernel, the new coordinate follows the law of one step at the matrix
the history reaches. -/
theorem ctsPartialTraj_last_apply (β : ℝ) (u : Pressure N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Step N M) {B : Set (Step N M)} (hB : MeasurableSet B) :
    Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) n (n + 1) h
        ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
          x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' B)
      = stepLaw β ((Trajectory.ofStepHistory h).state u (n + 1)) B := by
  have hmeas : Measurable fun x : (i : Finset.Iic (n + 1)) → Step N M =>
      x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := measurable_pi_apply _
  rw [← Measure.map_apply hmeas hB, ← Kernel.map_apply _ hmeas,
    Kernel.map_partialTraj_succ_self, ctsDrivingKernel_apply]

/-- The law of the first holding time is exponential of rate `q_β (u)`. -/
theorem ctsPathMeasure_holdingTime_zero (β : ℝ) (u : Pressure N M) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ctsPathMeasure β u {ω | holdingTime 0 ω ∈ A} = expMeasure (totalRate β u) A := by
  have hset : {ω : ℕ → Step N M | holdingTime 0 ω ∈ A}
      = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) 0 ⁻¹'
        ((fun h : (i : Finset.Iic 0) → Step N M => (h ⟨0, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A) :=
    rfl
  have hmeas : MeasurableSet ((fun h : (i : Finset.Iic 0) → Step N M =>
      (h ⟨0, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A) :=
    (measurable_snd.comp (measurable_pi_apply _)) hA
  rw [hset, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hmeas,
    ctsPathMeasure_map_frestrictLe]
  unfold ctsHistoryMeasure
  rw [Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_apply measurable_toStepHistoryZero hmeas]
  exact stepLaw_preimage_snd β u A

/-- **The holding-time bound.**  If, after every history of the first `n + 1` expressions
lying in `G`, the holding time that follows has `expMeasure` mass at most `c` on `A`, then the
event that the history lies in `G` and that holding time lands in `A` has probability at most
`c`. -/
theorem ctsPathMeasure_history_holdingTime_le (β : ℝ) (u : Pressure N M) (n : ℕ)
    {G : Set ((i : Finset.Iic n) → Step N M)} (hmeasG : MeasurableSet G) {A : Set ℝ}
    (hA : MeasurableSet A) {c : ℝ≥0∞}
    (hc : ∀ h ∈ G, expMeasure (totalRate β ((Trajectory.ofStepHistory h).state u (n + 1))) A ≤ c) :
    ctsPathMeasure β u ((Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G)
        ∩ {ω | holdingTime (n + 1) ω ∈ A}) ≤ c := by
  set S : Set ((i : Finset.Iic (n + 1)) → Step N M) :=
    (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.le_succ n) ⁻¹' G) ∩
      ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
        (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A) with hS
  have hmeasLast : MeasurableSet ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
      (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A) :=
    (measurable_snd.comp (measurable_pi_apply _)) hA
  have hmeasS : MeasurableSet S :=
    ((Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Step N M) (Nat.le_succ n)) hmeasG).inter
      hmeasLast
  have hsplit : (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G)
        ∩ {ω : ℕ → Step N M | holdingTime (n + 1) ω ∈ A}
      = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) (n + 1) ⁻¹' S := rfl
  rw [hsplit, ← Measure.map_apply (Preorder.measurable_frestrictLe (n + 1)) hmeasS,
    ctsPathMeasure_map_frestrictLe]
  have hstep : ctsHistoryMeasure β u (n + 1) S
      = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
          (ctsDrivingKernel β u) n (n + 1) h S ∂(ctsHistoryMeasure β u n) := by
    unfold ctsHistoryMeasure
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
      Measure.bind_apply hmeasS (Kernel.aemeasurable _)]
  rw [hstep]
  calc ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
        (ctsDrivingKernel β u) n (n + 1) h S ∂(ctsHistoryMeasure β u n)
      ≤ ∫⁻ _, c ∂(ctsHistoryMeasure β u n) := by
        refine lintegral_mono fun h => ?_
        by_cases hh : h ∈ G
        · refine le_trans (measure_mono Set.inter_subset_right) ?_
          have hcomp : ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
                (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A)
              = (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
                  x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
                ((fun z : Step N M => z.2) ⁻¹' A) := rfl
          rw [hcomp, ctsPartialTraj_last_apply β u n h (measurable_snd hA),
            stepLaw_preimage_snd]
          exact hc h hh
        · refine le_trans (measure_mono Set.inter_subset_left) ?_
          rw [ctsPartialTraj_frestrictLe₂_apply β u n h hmeasG,
            Measure.dirac_apply' _ hmeasG, Set.indicator_of_notMem hh]
          exact zero_le
    _ = c := by rw [lintegral_const, measure_univ, mul_one]

/-- The greedy specialisation of the holding-time bound. -/
theorem ctsPathMeasure_greedy_holdingTime_le (β : ℝ) (u : Pressure N M) (n : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) {c : ℝ≥0∞}
    (hc : ∀ h ∈ ctsGreedyHistory u n,
      expMeasure (totalRate β ((Trajectory.ofStepHistory h).state u (n + 1))) A ≤ c) :
    ctsPathMeasure β u (ctsGreedyEvents u (n + 1) ∩ {ω | holdingTime (n + 1) ω ∈ A}) ≤ c := by
  rw [ctsGreedyEvents_eq_preimage]
  exact ctsPathMeasure_history_holdingTime_le β u n (measurableSet_ctsGreedyHistory u n) hA hc

/-- The unconditional holding-time bound. -/
theorem ctsPathMeasure_holdingTime_succ_le (β : ℝ) (u : Pressure N M) (n : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) {c : ℝ≥0∞}
    (hc : ∀ h : (i : Finset.Iic n) → Step N M,
      expMeasure (totalRate β ((Trajectory.ofStepHistory h).state u (n + 1))) A ≤ c) :
    ctsPathMeasure β u {ω | holdingTime (n + 1) ω ∈ A} ≤ c := by
  have huniv : {ω : ℕ → Step N M | holdingTime (n + 1) ω ∈ A}
      = (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' Set.univ)
        ∩ {ω : ℕ → Step N M | holdingTime (n + 1) ω ∈ A} := by
    rw [Set.preimage_univ, Set.univ_inter]
  rw [huniv]
  exact ctsPathMeasure_history_holdingTime_le β u n MeasurableSet.univ hA fun h _ => hc h

/-! ### Off the zero matrix, the total rate is at least `e^{β/(M-1)}` -/

omit [NeZero N] [NeZero M] in
/-- A state of `S` other than the zero matrix has an entry at least `1`. -/
theorem exists_one_le_of_ne_zero {v : Pressure N M} (hv : IsState v) (hv0 : v ≠ 0) :
    ∃ a o, 1 ≤ v a o := by
  obtain ⟨a, o, hao⟩ : ∃ a o, v a o ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (funext fun a => funext fun o => hcon a o)
  by_cases hpos : 0 < v a o
  · exact ⟨a, o, hpos⟩
  · have hne : ∃ p, 0 < v a p := by
      by_contra hcon
      push Not at hcon
      have hzero : ∀ p ∈ Finset.univ, v a p = 0 :=
        (Finset.sum_eq_zero_iff_of_nonpos fun p _ => hcon p).1 (hv.trust_eq_zero a)
      exact hao (hzero o (Finset.mem_univ o))
    obtain ⟨p, hp⟩ := hne
    exact ⟨a, p, hp⟩

omit [NeZero N] [NeZero M] in
/-- Off the zero matrix, the total jump rate out of a state of `S` is at least
`e^{β/(M-1)}`: some entry is at least `1`, and every rate is positive. -/
theorem exp_le_totalRate (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {v : Pressure N M}
    (hv : IsState v) (hv0 : v ≠ 0) :
    Real.exp (β / ((M : ℝ) - 1)) ≤ totalRate β v := by
  obtain ⟨a, o, hao⟩ := exists_one_le_of_ne_zero hv hv0
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have h1 : (1 : ℝ) ≤ (v a o : ℝ) := by exact_mod_cast hao
  have hterm : Real.exp (β / ((M : ℝ) - 1)) ≤ jumpRate β v a o := by
    rw [jumpRate]
    refine Real.exp_le_exp.2 ?_
    rw [div_le_div_iff_of_pos_right hM1]
    nlinarith
  refine hterm.trans ?_
  rw [totalRate]
  exact Finset.single_le_sum (f := fun p : Jump N M => jumpRate β v p.1 p.2)
    (fun p _ => (jumpRate_pos β v p.1 p.2).le) (Finset.mem_univ (a, o))

omit [NeZero N] [NeZero M] in
/-- **The greedy run never sits at the zero matrix.**  The zero row that `S` provides has to
be the row of the actor that expressed, and then the entry it expressed was `0` while some
other entry was `1` --- which no greedy expression allows. -/
theorem state_ne_zero_of_greedy (hM : 2 ≤ M) (hN : 2 ≤ N) {T : Trajectory N M}
    {u : Pressure N M} (hu : IsState u) (hu0 : u ≠ 0) {n : ℕ}
    (hg : ∀ k < n, IsGreedyAt T u k) : T.state u n ≠ 0 := by
  cases n with
  | zero => simpa using hu0
  | succ m =>
      intro hzero
      set v := T.state u m with hv
      set a := T.actor m with ha
      set o := T.opinion m with ho
      have hvS : IsState v := T.isState_state hu m
      have hgm : ∀ b p, v b p ≤ v a o := hg m (by omega)
      have hstep : T.state u (m + 1) = express a o v := Trajectory.state_succ T u m
      rw [hstep] at hzero
      have hentry : ∀ b p, express a o v b p = 0 := fun b p => by
        rw [hzero]; rfl
      obtain ⟨c, hc⟩ := hvS.exists_zero_row
      by_cases hca : c = a
      · have hco : v a o = 0 := by rw [← hca]; exact hc o
        obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
          (show 1 < Fintype.card (Actor N) by simp only [Fintype.card_fin]; omega) a
        obtain ⟨p, hp⟩ := Fintype.exists_ne_of_one_lt_card
          (show 1 < Fintype.card (Opinion M) by simp only [Fintype.card_fin]; omega) o
        have hbp := hentry b p
        rw [express, if_neg hb, if_neg hp] at hbp
        have hge : (1 : ℤ) ≤ v b p := by omega
        have hle := hgm b p
        omega
      · have hcc := hentry c o
        rw [express, if_neg hca, if_pos rfl, hc o] at hcc
        have : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
        omega

/-! ### Each holding time of a greedy run is dominated by `Exp (e^{β/(M-1)})` -/

theorem expMeasure_Ioi_le (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {v : Pressure N M}
    (hv : IsState v) (hv0 : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    expMeasure (totalRate β v) (Set.Ioi s)
      ≤ ENNReal.ofReal (Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * s))) := by
  rw [expMeasure_Ioi_of_nonneg (totalRate_pos β v) hs]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := exp_le_totalRate hM hβ hv hv0
  nlinarith [Real.exp_pos (β / ((M : ℝ) - 1))]

theorem ctsPathMeasure_greedy_holdingTime_gt (hM : 2 ≤ M) (hN : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {u : Pressure N M} (hu : IsState u) (hu0 : u ≠ 0) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ctsPathMeasure β u (ctsGreedyEvents u n ∩ {ω | s < holdingTime n ω})
      ≤ ENNReal.ofReal (Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * s))) := by
  cases n with
  | zero =>
      refine le_trans (measure_mono Set.inter_subset_right) ?_
      have hset : {ω : ℕ → Step N M | s < holdingTime 0 ω}
          = {ω : ℕ → Step N M | holdingTime 0 ω ∈ Set.Ioi s} := rfl
      rw [hset, ctsPathMeasure_holdingTime_zero β u measurableSet_Ioi]
      exact expMeasure_Ioi_le hM hβ hu hu0 hs
  | succ m =>
      refine ctsPathMeasure_greedy_holdingTime_le β u m measurableSet_Ioi fun h hh => ?_
      refine expMeasure_Ioi_le hM hβ ((Trajectory.ofStepHistory h).isState_state hu (m + 1)) ?_ hs
      exact state_ne_zero_of_greedy hM hN hu hu0 fun k hk => hh k (by omega)

/-- The closed form of the tail bound. -/
theorem expMeasure_Ici_le (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {v : Pressure N M}
    (hv : IsState v) (hv0 : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    expMeasure (totalRate β v) (Set.Ici s)
      ≤ ENNReal.ofReal (Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * s))) := by
  rw [expMeasure_Ici_of_nonneg (totalRate_pos β v) hs]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := exp_le_totalRate hM hβ hv hv0
  nlinarith [Real.exp_pos (β / ((M : ℝ) - 1))]

/-- The closed form of the greedy holding-time bound, which is what Remark 6 uses. -/
theorem ctsPathMeasure_greedy_holdingTime_ge (hM : 2 ≤ M) (hN : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {u : Pressure N M} (hu : IsState u) (hu0 : u ≠ 0) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ctsPathMeasure β u (ctsGreedyEvents u n ∩ {ω | s ≤ holdingTime n ω})
      ≤ ENNReal.ofReal (Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * s))) := by
  cases n with
  | zero =>
      refine le_trans (measure_mono Set.inter_subset_right) ?_
      have hset : {ω : ℕ → Step N M | s ≤ holdingTime 0 ω}
          = {ω : ℕ → Step N M | holdingTime 0 ω ∈ Set.Ici s} := rfl
      rw [hset, ctsPathMeasure_holdingTime_zero β u measurableSet_Ici]
      exact expMeasure_Ici_le hM hβ hu hu0 hs
  | succ m =>
      refine ctsPathMeasure_greedy_holdingTime_le β u m measurableSet_Ici fun h hh => ?_
      refine expMeasure_Ici_le hM hβ ((Trajectory.ofStepHistory h).isState_state hu (m + 1)) ?_ hs
      exact state_ne_zero_of_greedy hM hN hu hu0 fun k hk => hh k (by omega)

/-! ### The holding times are almost surely positive -/

theorem ctsPathMeasure_holdingTime_nonpos (β : ℝ) (u : Pressure N M) (n : ℕ) :
    ctsPathMeasure β u {ω | holdingTime n ω ≤ 0} = 0 := by
  have hzero : ∀ v : Pressure N M, expMeasure (totalRate β v) (Set.Iic 0) = 0 := fun v =>
    expMeasure_Iic_zero (totalRate_pos β v)
  cases n with
  | zero =>
      have hset : {ω : ℕ → Step N M | holdingTime 0 ω ≤ 0}
          = {ω : ℕ → Step N M | holdingTime 0 ω ∈ Set.Iic (0 : ℝ)} := rfl
      rw [hset, ctsPathMeasure_holdingTime_zero β u measurableSet_Iic]
      exact hzero u
  | succ m =>
      refine le_antisymm ?_ zero_le
      have hset : {ω : ℕ → Step N M | holdingTime (m + 1) ω ≤ 0}
          = {ω : ℕ → Step N M | holdingTime (m + 1) ω ∈ Set.Iic (0 : ℝ)} := rfl
      rw [hset]
      exact ctsPathMeasure_holdingTime_succ_le β u m measurableSet_Iic
        (c := 0) fun h => le_of_eq (hzero _)

/-! ### From the skeleton to the clock -/

omit [NeZero N] [NeZero M] in
theorem measurableSet_ctsGreedyEvents (u : Pressure N M) (n : ℕ) :
    MeasurableSet (ctsGreedyEvents u n) := by
  cases n with
  | zero =>
      have : ctsGreedyEvents u 0 = Set.univ := by ext ω; simp [ctsGreedyEvents]
      rw [this]; exact MeasurableSet.univ
  | succ m =>
      rw [ctsGreedyEvents_eq_preimage]
      exact (Preorder.measurable_frestrictLe m) (measurableSet_ctsGreedyHistory u m)

omit [NeZero N] [NeZero M] in
/-- On a realisation whose holding times are all positive, the jump count at `T_k` is `k`. -/
theorem jumpCount_jumpTime (ω : ℕ → Step N M) (hpos : ∀ n, 0 < holdingTime n ω) {k : ℕ}
    (hk : k ≠ 0) : jumpCount ω (jumpTime k ω) = k := by
  have hmono : StrictMono fun n => jumpTime n ω := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    rw [jumpTime_succ]
    linarith [hpos n]
  rw [jumpCount_eq_iff (jumpTime k ω) ω hk]
  exact ⟨le_rfl, fun m hm => hmono.le_iff_le.1 hm⟩

omit [NeZero N] [NeZero M] in
/-- If the `k`-th matrix of a realisation is already in `θ`, the hitting time of `θ` is at
most the `k`-th jump time. -/
theorem hittingTimeCts_le_jumpTime {u : Pressure N M} {θ : Set (Pressure N M)}
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) {k : ℕ} (hk : k ≠ 0)
    (hmem : (Trajectory.ofStepPath ω).state u k ∈ θ) :
    hittingTimeCts u θ ω ≤ ENNReal.ofReal (jumpTime k ω) := by
  refine sInf_le ⟨jumpTime k ω, ⟨?_, ?_⟩, rfl⟩
  · exact Finset.sum_nonneg fun n _ => (hpos n).le
  · rw [process, jumpCount_jumpTime ω hpos hk]
    exact hmem

omit [NeZero N] [NeZero M] in
/-- The mirror: if none of the first `k + 1` matrices of a realisation lies in `θ`, the hitting
time of `θ` is strictly beyond the `k`-th jump time.  Before `T_{k+1}` the process shows those
matrices and no others, so `θ` is not met there.

This is what says, in Remark 6, that the greedy run has not reached `C^{-o}` by the time it
reaches `L^o`. -/
theorem jumpTime_lt_hittingTimeCts {u : Pressure N M} {θ : Set (Pressure N M)}
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) {k : ℕ}
    (hmem : ∀ n ≤ k, (Trajectory.ofStepPath ω).state u n ∉ θ) :
    ENNReal.ofReal (jumpTime k ω) < hittingTimeCts u θ ω := by
  have hmono : StrictMono fun n => jumpTime n ω := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    rw [jumpTime_succ]
    linarith [hpos n]
  have hnn : 0 ≤ jumpTime k ω := Finset.sum_nonneg fun n _ => (hpos n).le
  have hstep : ENNReal.ofReal (jumpTime k ω) < ENNReal.ofReal (jumpTime (k + 1) ω) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).2 (hmono (Nat.lt_succ_self k))
  refine lt_of_lt_of_le hstep (le_sInf ?_)
  rintro x ⟨t, ⟨ht0, htθ⟩, rfl⟩
  refine ENNReal.ofReal_le_ofReal ?_
  by_contra hcon
  have hlt : t < jumpTime (k + 1) ω := not_le.1 hcon
  have hub : ∀ n ∈ {n : ℕ | jumpTime n ω ≤ t}, n ≤ k := by
    intro n hn
    by_contra hnk
    have hle : jumpTime (k + 1) ω ≤ jumpTime n ω := hmono.monotone (by omega)
    have : jumpTime n ω ≤ t := hn
    linarith
  have hcount : jumpCount ω t ≤ k := by
    rcases Set.eq_empty_or_nonempty {n : ℕ | jumpTime n ω ≤ t} with he | hne
    · rw [jumpCount, he]; simp
    · exact csSup_le hne hub
  exact hmem (jumpCount ω t) hcount htθ

end HoldingTimes

/-! ### Restarting the process at the first jump

Corollary 11 and equation (19) both read the process after its first expression: the waiting
time `τ = T₁` at the start, and then a process started at the matrix that expression reaches.
Nothing in `SocialNetwork.Skeleton` restarts the continuous-time process --- `Trajectory.shift`
restarts the skeleton, which carries no clock --- so the restart is built here.

It is the Markov property at time `1` for the jump-hold representation, and it is exact: the
driving kernel reads the history only through the matrix it reaches, and dropping the first
step of a history shifts that reading by one.  The work is in three steps.

* `SocialNetwork.ctsPartialTraj_succ_apply` describes one step of the kernel explicitly --- the
  history is kept and one more step is drawn from `stepLaw` at the matrix it reaches --- which
  turns the shift into a statement about `SocialNetwork.stepLaw` alone.
* `SocialNetwork.map_ctsPartialTraj_shiftStepHistory` is the induction on the length of the
  history, and `SocialNetwork.map_ctsTraj_shiftStepPath` passes to whole realisations by
  checking the two laws on cylinders.
* `SocialNetwork.hittingTimeCts_le_shift` is the pointwise half: with every holding time
  positive, the hitting time from `u` is at most `T₁` plus the hitting time of the shifted
  realisation.  Its proof splits on whether the shifted jump counter is finite at the time in
  question; on the explosion event, where the counter is junk on both sides, the matrix at
  stake is the one the first expression reaches, shown at `T₁` itself.  Non-explosion
  (Theorem 1.1) would remove that case, and is not available.

**No counterpart among the numbered statements of the paper**, which restarts the process at
`τ` without comment. -/

section Restart

/-- The realisation shifted past its first step. -/
def shiftStepPath (ω : ℕ → Step N M) : ℕ → Step N M := fun i => ω (1 + i)

theorem measurable_shiftStepPath : Measurable (shiftStepPath (N := N) (M := M)) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (1 + i)

/-- A history of the first `n + 2` steps, shifted past its first entry. -/
def shiftStepHistory (n : ℕ) (x : (i : Finset.Iic (n + 1)) → Step N M) :
    (i : Finset.Iic n) → Step N M :=
  fun i => x ⟨1 + i.1, Finset.mem_Iic.2 (by have := Finset.mem_Iic.1 i.2; omega)⟩

theorem measurable_shiftStepHistory (n : ℕ) :
    Measurable (shiftStepHistory (N := N) (M := M) n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- A history of the first `n + 1` steps, extended by one more step. -/
def extendStepHistory {n : ℕ} (x : (i : Finset.Iic n) → Step N M) (z : Step N M) :
    (i : Finset.Iic (n + 1)) → Step N M :=
  fun i => if h : i.1 ≤ n then x ⟨i.1, Finset.mem_Iic.2 h⟩ else z

theorem measurable_extendStepHistory {n : ℕ} (x : (i : Finset.Iic n) → Step N M) :
    Measurable (extendStepHistory x) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i.1 ≤ n
  · simp [extendStepHistory, h]
  · simpa [extendStepHistory, h] using measurable_id'

theorem shiftStepHistory_extendStepHistory {n : ℕ}
    (x : (i : Finset.Iic (n + 1)) → Step N M) (z : Step N M) :
    shiftStepHistory (n + 1) (extendStepHistory x z)
      = extendStepHistory (shiftStepHistory n x) z := by
  funext i
  have hi : i.1 ≤ n + 1 := Finset.mem_Iic.1 i.2
  simp only [shiftStepHistory, extendStepHistory]
  by_cases h : i.1 ≤ n
  · rw [dif_pos (by omega), dif_pos h]
  · rw [dif_neg (by omega), dif_neg h]

theorem frestrictLe_shiftStepPath (n : ℕ) (ω : ℕ → Step N M) :
    Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n (shiftStepPath ω)
      = shiftStepHistory n (Preorder.frestrictLe (n + 1) ω) := rfl

theorem ofStepPath_shiftStepPath (ω : ℕ → Step N M) :
    Trajectory.ofStepPath (shiftStepPath ω) = (Trajectory.ofStepPath ω).shift 1 := rfl

/-- Replaying a shifted history from the state the first step reaches is replaying the whole
history one step further. -/
theorem state_ofStepHistory_shiftStepHistory (u : Pressure N M) {n : ℕ}
    (x : (i : Finset.Iic (n + 1)) → Step N M) {k : ℕ} (hk : k ≤ n + 1) :
    (Trajectory.ofStepHistory (shiftStepHistory n x)).state
        ((Trajectory.ofStepHistory x).state u 1) k
      = (Trajectory.ofStepHistory x).state u (1 + k) := by
  rw [Trajectory.state_add]
  refine Trajectory.state_congr _ k (fun j hj => ?_) (fun j hj => ?_)
  · rw [Trajectory.shift_actor]
    show (Trajectory.ofHistory fun i => ((shiftStepHistory n x) i).1).actor j
        = (Trajectory.ofHistory fun i => (x i).1).actor (1 + j)
    rw [Trajectory.ofHistory_actor _ (show j ≤ n by omega),
      Trajectory.ofHistory_actor _ (show 1 + j ≤ n + 1 by omega)]
    rfl
  · rw [Trajectory.shift_opinion]
    show (Trajectory.ofHistory fun i => ((shiftStepHistory n x) i).1).opinion j
        = (Trajectory.ofHistory fun i => (x i).1).opinion (1 + j)
    rw [Trajectory.ofHistory_opinion _ (show j ≤ n by omega),
      Trajectory.ofHistory_opinion _ (show 1 + j ≤ n + 1 by omega)]
    rfl

/-! ### One step of the driving kernel, explicitly -/

variable [NeZero N] [NeZero M]

omit [NeZero N] [NeZero M] in
theorem IicProdIoc_prodMk_piSingleton {n : ℕ} (x : (i : Finset.Iic n) → Step N M) :
    (IicProdIoc (X := fun _ : ℕ => Step N M) n (n + 1)) ∘ (Prod.mk x) ∘
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Step N M) n)
      = extendStepHistory x := by
  funext z i
  simp only [Function.comp_apply, IicProdIoc, extendStepHistory]
  by_cases h : i.1 ≤ n
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    simp only [MeasurableEquiv.piSingleton, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      eqRec_eq_cast, cast_eq]

/-- One step of the kernel keeps the history it started from and appends a step drawn from the
law at the matrix the history reaches. -/
theorem ctsPartialTraj_succ_apply (β : ℝ) (u : Pressure N M) (n : ℕ)
    (x : (i : Finset.Iic n) → Step N M) :
    Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) n (n + 1) x
      = (stepLaw β ((Trajectory.ofStepHistory x).state u (n + 1))).map (extendStepHistory x) := by
  have hpi : Measurable (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Step N M) n) :=
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Step N M) n).measurable
  have hIic : Measurable (IicProdIoc (X := fun _ : ℕ => Step N M) n (n + 1)) :=
    measurable_IicProdIoc
  have hmk : Measurable (Prod.mk (β := (i : Finset.Ioc n (n + 1)) → Step N M) x) :=
    measurable_prodMk_left
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hIic, Kernel.prod_apply,
    Kernel.id_apply, Kernel.map_apply _ hpi, ctsDrivingKernel_apply, Measure.dirac_prod,
    Measure.map_map hmk hpi, Measure.map_map hIic (hmk.comp hpi),
    IicProdIoc_prodMk_piSingleton]

/-! ### Restarting the process at the first jump -/

omit [NeZero N] [NeZero M] in
theorem shiftStepHistory_zero_comp (y : (i : Finset.Iic 0) → Step N M) :
    (shiftStepHistory (N := N) (M := M) 0) ∘ (extendStepHistory y) = toStepHistoryZero := by
  funext z i
  simp only [Function.comp_apply, shiftStepHistory, extendStepHistory, toStepHistoryZero]
  rw [dif_neg (by omega)]

omit [NeZero N] [NeZero M] in
theorem state_one_frestrictLe₂ (u : Pressure N M) {n : ℕ}
    (x : (i : Finset.Iic (n + 1)) → Step N M) :
    (Trajectory.ofStepHistory x).state u 1
      = (Trajectory.ofStepHistory (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M)
          (Nat.zero_le (n + 1)) x)).state u 1 := by
  refine Trajectory.state_congr u 1 (fun j hj => ?_) (fun j hj => ?_)
  · have hj0 : j = 0 := by omega
    subst hj0
    show (Trajectory.ofHistory fun i => (x i).1).actor 0
      = (Trajectory.ofHistory fun i =>
          ((Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.zero_le (n + 1)) x) i).1).actor 0
    rw [Trajectory.ofHistory_actor _ (Nat.zero_le (n + 1)),
      Trajectory.ofHistory_actor _ (le_refl 0)]
    rfl
  · have hj0 : j = 0 := by omega
    subst hj0
    show (Trajectory.ofHistory fun i => (x i).1).opinion 0
      = (Trajectory.ofHistory fun i =>
          ((Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.zero_le (n + 1)) x) i).1).opinion 0
    rw [Trajectory.ofHistory_opinion _ (Nat.zero_le (n + 1)),
      Trajectory.ofHistory_opinion _ (le_refl 0)]
    rfl

/-- **The restart at the first jump, on histories.**  From a fixed first step, the history of
the steps that follow is the history of the process started at the matrix that step reaches. -/
theorem map_ctsPartialTraj_shiftStepHistory (β : ℝ) (u : Pressure N M) (n : ℕ)
    (y : (i : Finset.Iic 0) → Step N M) :
    (Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0 (n + 1) y).map
        (shiftStepHistory n)
      = ctsHistoryMeasure β ((Trajectory.ofStepHistory y).state u 1) n := by
  induction n with
  | zero =>
      rw [ctsPartialTraj_succ_apply, Measure.map_map (measurable_shiftStepHistory 0)
        (measurable_extendStepHistory y), shiftStepHistory_zero_comp]
      unfold ctsHistoryMeasure
      rw [Kernel.partialTraj_self, Measure.id_comp]
  | succ n ih =>
      set v := (Trajectory.ofStepHistory y).state u 1 with hv
      have hae : ∀ᵐ x ∂(Kernel.partialTraj (X := fun _ : ℕ => Step N M)
          (ctsDrivingKernel β u) 0 (n + 1) y), (Trajectory.ofStepHistory x).state u 1 = v := by
        have hmap : (Kernel.partialTraj (X := fun _ : ℕ => Step N M)
              (ctsDrivingKernel β u) 0 (n + 1) y).map
            (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
              (Trajectory.ofStepHistory x).state u 1) = Measure.dirac v := by
          have hcomp : (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
                (Trajectory.ofStepHistory x).state u 1)
              = (fun h : (i : Finset.Iic 0) → Step N M =>
                  (Trajectory.ofStepHistory h).state u 1) ∘
                (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.zero_le (n + 1))) :=
            funext fun x => state_one_frestrictLe₂ u x
          rw [hcomp, ← Measure.map_map
              (measurable_stepHistoryState u 0 1)
              (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Step N M) (Nat.zero_le (n + 1))),
            Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Step N M) y
              (Nat.zero_le (n + 1)), Kernel.partialTraj_self, Kernel.id_apply,
            Measure.map_dirac' (measurable_stepHistoryState u 0 1) y]
        rw [Filter.eventually_iff, mem_ae_iff]
        have hset : {x : (i : Finset.Iic (n + 1)) → Step N M |
              (Trajectory.ofStepHistory x).state u 1 = v}ᶜ
            = (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
                (Trajectory.ofStepHistory x).state u 1) ⁻¹' {v}ᶜ := rfl
        rw [hset, ← Measure.map_apply (measurable_stepHistoryState u (n + 1) 1)
            MeasurableSet.of_discrete, hmap,
          Measure.dirac_apply' _ MeasurableSet.of_discrete]
        simp
      ext S hS
      have hpt : ∀ x : (i : Finset.Iic (n + 1)) → Step N M,
          (Trajectory.ofStepHistory x).state u 1 = v →
          Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) (n + 1) (n + 2) x
              (shiftStepHistory (n + 1) ⁻¹' S)
            = Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β v) n (n + 1)
                (shiftStepHistory n x) S := by
        intro x hx
        rw [ctsPartialTraj_succ_apply, ctsPartialTraj_succ_apply,
          Measure.map_apply (measurable_extendStepHistory x)
            ((measurable_shiftStepHistory (n + 1)) hS),
          Measure.map_apply (measurable_extendStepHistory (shiftStepHistory n x)) hS]
        have hpre : extendStepHistory x ⁻¹' (shiftStepHistory (n + 1) ⁻¹' S)
            = extendStepHistory (shiftStepHistory n x) ⁻¹' S := by
          rw [← Set.preimage_comp]
          exact congrArg (fun f => f ⁻¹' S)
            (funext fun z => shiftStepHistory_extendStepHistory x z)
        have hstate : (Trajectory.ofStepHistory (shiftStepHistory n x)).state v (n + 1)
            = (Trajectory.ofStepHistory x).state u (n + 1 + 1) := by
          rw [← hx, state_ofStepHistory_shiftStepHistory u x (le_refl (n + 1)),
            show 1 + (n + 1) = n + 1 + 1 from by omega]
        rw [hpre, hstate]
      have hstep : ctsHistoryMeasure β v (n + 1) S
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β v)
              n (n + 1) h S ∂(ctsHistoryMeasure β v n) := by
        unfold ctsHistoryMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply hS (Kernel.aemeasurable _)]
      rw [Measure.map_apply (measurable_shiftStepHistory (n + 1)) hS,
        Kernel.partialTraj_succ_eq_comp (Nat.zero_le (n + 1)),
        Kernel.comp_apply' _ _ _ ((measurable_shiftStepHistory (n + 1)) hS), hstep]
      calc ∫⁻ x, Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u)
              (n + 1) (n + 1 + 1) x (shiftStepHistory (n + 1) ⁻¹' S)
            ∂(Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0 (n + 1) y)
          = ∫⁻ x, Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β v)
                n (n + 1) (shiftStepHistory n x) S
              ∂(Kernel.partialTraj (X := fun _ : ℕ => Step N M)
                (ctsDrivingKernel β u) 0 (n + 1) y) :=
            lintegral_congr_ae (hae.mono fun x hx => hpt x hx)
        _ = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β v)
                n (n + 1) h S
              ∂((Kernel.partialTraj (X := fun _ : ℕ => Step N M)
                (ctsDrivingKernel β u) 0 (n + 1) y).map (shiftStepHistory n)) :=
            (lintegral_map (Kernel.measurable_coe _ hS) (measurable_shiftStepHistory n)).symm
        _ = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β v)
                n (n + 1) h S ∂(ctsHistoryMeasure β v n) := by rw [ih]

omit [NeZero N] [NeZero M] in
/-- The matrix the first expression of a history reaches. -/
theorem state_one_ofStepHistory (u : Pressure N M) {n : ℕ}
    (h : (i : Finset.Iic n) → Step N M) :
    (Trajectory.ofStepHistory h).state u 1
      = express (h ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩).1.1
          (h ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩).1.2 u := by
  rw [Trajectory.state_succ, Trajectory.state_zero]
  show express ((Trajectory.ofHistory fun i => (h i).1).actor 0)
      ((Trajectory.ofHistory fun i => (h i).1).opinion 0) u = _
  rw [Trajectory.ofHistory_actor _ (Nat.zero_le n),
    Trajectory.ofHistory_opinion _ (Nat.zero_le n)]

/-- **The restart at the first jump, on realisations.**  From a fixed first step, the rest of
the realisation is a realisation of the process started at the matrix that step reaches. -/
theorem map_ctsTraj_shiftStepPath (β : ℝ) (u : Pressure N M)
    (y : (i : Finset.Iic 0) → Step N M) :
    (Kernel.traj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0 y).map shiftStepPath
      = ctsPathMeasure β ((Trajectory.ofStepHistory y).state u 1) := by
  have hprob : IsProbabilityMeasure
      ((Kernel.traj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0 y).map
        shiftStepPath) :=
    Measure.isProbabilityMeasure_map measurable_shiftStepPath.aemeasurable
  refine MeasureTheory.ext_of_generate_finite
    {s : Set (ℕ → Step N M) | ∃ (b : ℕ) (T : Set ((i : Finset.Iic b) → Step N M)),
      MeasurableSet T ∧ s = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) b ⁻¹' T}
    ?_ ?_ ?_ ?_
  · refine le_antisymm (iSup_le fun i => ?_) (MeasurableSpace.generateFrom_le ?_)
    · rintro s ⟨T, hT, rfl⟩
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨i, (fun h : (j : Finset.Iic i) → Step N M => h ⟨i, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' T,
          (measurable_pi_apply _) hT, rfl⟩
    · rintro s ⟨b, T, hT, rfl⟩
      exact Preorder.measurable_frestrictLe b hT
  · rintro s ⟨b, T, hT, rfl⟩ t ⟨b', T', hT', rfl⟩ -
    rcases le_total b b' with hbb | hbb
    · exact ⟨b', (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) hbb ⁻¹' T) ∩ T',
        ((Preorder.measurable_frestrictLe₂ hbb) hT).inter hT',
        by rw [Set.preimage_inter, ← Set.preimage_comp]; rfl⟩
    · exact ⟨b, T ∩ (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) hbb ⁻¹' T'),
        hT.inter ((Preorder.measurable_frestrictLe₂ hbb) hT'),
        by rw [Set.preimage_inter, ← Set.preimage_comp]; rfl⟩
  · rintro s ⟨b, T, hT, rfl⟩
    have hpre : shiftStepPath ⁻¹' (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) b ⁻¹' T)
        = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) (b + 1) ⁻¹'
          (shiftStepHistory b ⁻¹' T) := rfl
    rw [Measure.map_apply measurable_shiftStepPath (Preorder.measurable_frestrictLe b hT),
      hpre, ← Measure.map_apply (Preorder.measurable_frestrictLe (b + 1))
        ((measurable_shiftStepHistory b) hT),
      Kernel.traj_map_frestrictLe_apply, ← Measure.map_apply (measurable_shiftStepHistory b) hT,
      map_ctsPartialTraj_shiftStepHistory,
      ← Measure.map_apply (Preorder.measurable_frestrictLe b) hT, ctsPathMeasure_map_frestrictLe]
  · rw [measure_univ, measure_univ]

/-- **The restart at the first jump.**  The first step is drawn from `stepLaw β u`, and given
it the rest of the realisation is a realisation of the process started at the matrix it
reaches.

**No counterpart among the numbered statements of the paper**, which uses it without comment
in the proof of Corollary 11 and in equation (19). -/
theorem ctsPathMeasure_restart (β : ℝ) (u : Pressure N M) {B : Set (Step N M)}
    (hB : MeasurableSet B) {E : Set (ℕ → Step N M)} (hE : MeasurableSet E) :
    ctsPathMeasure β u ({ω | ω 0 ∈ B} ∩ shiftStepPath ⁻¹' E)
      = ∫⁻ z in B, ctsPathMeasure β (express z.1.1 z.1.2 u) E ∂(stepLaw β u) := by
  have hS : MeasurableSet ({ω : ℕ → Step N M | ω 0 ∈ B} ∩ shiftStepPath ⁻¹' E) :=
    ((measurable_pi_apply 0) hB).inter (measurable_shiftStepPath hE)
  have hzero : ∀ z : Step N M,
      Kernel.traj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0 (toStepHistoryZero z)
          ({ω : ℕ → Step N M | ω 0 ∈ B} ∩ shiftStepPath ⁻¹' E)
        = Set.indicator B (fun w : Step N M => ctsPathMeasure β (express w.1.1 w.1.2 u) E) z := by
    intro z
    have hmeasc : MeasurableSet ({h : (i : Finset.Iic 0) → Step N M |
        h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = z}ᶜ) := by
      have hset : {h : (i : Finset.Iic 0) → Step N M | h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = z}ᶜ
          = (fun h : (i : Finset.Iic 0) → Step N M => h ⟨0, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' {z}ᶜ :=
        rfl
      rw [hset]
      exact (measurable_pi_apply _) (measurableSet_singleton z).compl
    have hcoord : Kernel.traj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0
        (toStepHistoryZero z) ({ω : ℕ → Step N M | ω 0 = z}ᶜ) = 0 := by
      have h1 : ({ω : ℕ → Step N M | ω 0 = z}ᶜ)
          = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) 0 ⁻¹'
            ({h : (i : Finset.Iic 0) → Step N M | h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = z}ᶜ) := rfl
      rw [h1, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hmeasc,
        Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply,
        Measure.dirac_apply' _ hmeasc,
        Set.indicator_of_notMem (by simp [toStepHistoryZero])]
    have hshift : Kernel.traj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) 0
        (toStepHistoryZero z) (shiftStepPath ⁻¹' E)
        = ctsPathMeasure β (express z.1.1 z.1.2 u) E := by
      rw [← Measure.map_apply measurable_shiftStepPath hE, map_ctsTraj_shiftStepPath,
        state_one_ofStepHistory]
      rfl
    by_cases hzB : z ∈ B
    · rw [Set.indicator_of_mem hzB, ← hshift]
      refine le_antisymm (measure_mono Set.inter_subset_right) ?_
      refine le_measure_of_inter hcoord (le_refl _) ?_
      rintro ω ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      show ω 0 ∈ B
      rw [show ω 0 = z from h1]
      exact hzB
    · rw [Set.indicator_of_notMem hzB]
      refine le_antisymm ?_ (by simp)
      rw [← hcoord]
      refine measure_mono ?_
      rintro ω ⟨h1, -⟩ hcon
      apply hzB
      rw [← show ω 0 = z from hcon]
      exact h1
  rw [ctsPathMeasure, Measure.bind_apply hS (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hS) measurable_toStepHistoryZero,
    lintegral_congr hzero, lintegral_indicator hB]

/-! ### The hitting time after the first jump -/

omit [NeZero N] [NeZero M] in
theorem holdingTime_shiftStepPath (n : ℕ) (ω : ℕ → Step N M) :
    holdingTime n (shiftStepPath ω) = holdingTime (n + 1) ω := by
  show (ω (1 + n)).2 = (ω (n + 1)).2
  rw [Nat.add_comm]

omit [NeZero N] [NeZero M] in
theorem jumpTime_succ_shiftStepPath (n : ℕ) (ω : ℕ → Step N M) :
    jumpTime (n + 1) ω = holdingTime 0 ω + jumpTime n (shiftStepPath ω) := by
  have h1 : jumpTime (n + 1) ω
      = (∑ i ∈ Finset.range n, holdingTime (i + 1) ω) + holdingTime 0 ω :=
    Finset.sum_range_succ' _ n
  have h2 : jumpTime n (shiftStepPath ω) = ∑ i ∈ Finset.range n, holdingTime (i + 1) ω :=
    Finset.sum_congr rfl fun k _ => holdingTime_shiftStepPath k ω
  rw [h1, h2, add_comm]

omit [NeZero N] [NeZero M] in
theorem jumpTime_pos {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) {n : ℕ}
    (hn : 0 < n) : 0 < jumpTime n ω :=
  Finset.sum_pos (fun i _ => hpos i) ⟨0, Finset.mem_range.2 hn⟩

omit [NeZero N] [NeZero M] in
/-- **The process restarts at the first jump.**  With every holding time positive, every matrix
the shifted realisation shows at time `s` is one the realisation itself shows at some time no
later than `T₁ + s`.

The two cases are the two ways the jump counter can behave: below the explosion time it is
`1 + ` the counter of the shifted realisation, and on the explosion event --- where the counter
is junk on both sides --- the matrix in question is the one the first expression reaches, shown
at `T₁` itself.

**No counterpart in the paper**, which restarts the process at `τ` without comment. -/
theorem exists_process_eq_shift (u : Pressure N M) {ω : ℕ → Step N M}
    (hpos : ∀ n, 0 < holdingTime n ω) {s : ℝ} (hs : 0 ≤ s) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ holdingTime 0 ω + s ∧
      process u t ω
        = process ((Trajectory.ofStepPath ω).state u 1) s (shiftStepPath ω) := by
  have hpos' : ∀ n, 0 < holdingTime n (shiftStepPath ω) := by
    intro n; rw [holdingTime_shiftStepPath]; exact hpos (n + 1)
  have hT : 0 < holdingTime 0 ω := hpos 0
  by_cases hbdd : BddAbove {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s}
  · have hne : {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s}.Nonempty :=
      ⟨0, by simpa using hs⟩
    have hmem := Nat.sSup_mem hne hbdd
    set m := sSup {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s} with hm
    have hcount' : jumpCount (shiftStepPath ω) s = m := hm.symm
    refine ⟨holdingTime 0 ω + s, by linarith, le_rfl, ?_⟩
    have hcount : jumpCount ω (holdingTime 0 ω + s) = m + 1 := by
      refine (jumpCount_eq_iff _ ω (Nat.succ_ne_zero m)).2 ⟨?_, ?_⟩
      · rw [jumpTime_succ_shiftStepPath]
        have : jumpTime m (shiftStepPath ω) ≤ s := hmem
        linarith
      · intro k hk
        cases k with
        | zero => omega
        | succ j =>
            rw [jumpTime_succ_shiftStepPath] at hk
            have hj : jumpTime j (shiftStepPath ω) ≤ s := by linarith
            have := le_csSup hbdd hj
            omega
    show (Trajectory.ofStepPath ω).state u (jumpCount ω (holdingTime 0 ω + s))
      = (Trajectory.ofStepPath (shiftStepPath ω)).state
          ((Trajectory.ofStepPath ω).state u 1) (jumpCount (shiftStepPath ω) s)
    rw [hcount, hcount', ofStepPath_shiftStepPath, ← Trajectory.state_add,
      show 1 + m = m + 1 from by omega]
  · have hcount' : jumpCount (shiftStepPath ω) s = 0 := Nat.sSup_of_not_bddAbove hbdd
    refine ⟨holdingTime 0 ω, hT.le, by linarith, ?_⟩
    have hcount : jumpCount ω (holdingTime 0 ω) = 1 := by
      refine (jumpCount_eq_iff _ ω one_ne_zero).2 ⟨?_, ?_⟩
      · rw [show (1 : ℕ) = 0 + 1 from rfl, jumpTime_succ_shiftStepPath]
        simp [jumpTime]
      · intro k hk
        rcases Nat.lt_or_ge k 2 with h | h
        · omega
        · exfalso
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          rw [jumpTime_succ_shiftStepPath] at hk
          have hj : 0 < j := by omega
          linarith [jumpTime_pos hpos' hj]
    show (Trajectory.ofStepPath ω).state u (jumpCount ω (holdingTime 0 ω))
      = (Trajectory.ofStepPath (shiftStepPath ω)).state
          ((Trajectory.ofStepPath ω).state u 1) (jumpCount (shiftStepPath ω) s)
    rw [hcount, hcount', Trajectory.state_zero]

omit [NeZero N] [NeZero M] in
/-- **The hitting time after the first jump.**  With every holding time positive, the hitting
time from `u` is at most the first holding time plus the hitting time of the shifted
realisation, started at the matrix the first expression reaches. -/
theorem hittingTimeCts_le_shift (u : Pressure N M) (θ : Set (Pressure N M))
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) :
    hittingTimeCts u θ ω
      ≤ ENNReal.ofReal (holdingTime 0 ω)
        + hittingTimeCts ((Trajectory.ofStepPath ω).state u 1) θ (shiftStepPath ω) := by
  unfold hittingTimeCts
  rw [ENNReal.add_sInf]
  refine le_iInf₂ fun b hb => ?_
  obtain ⟨s, ⟨hs0, hsθ⟩, rfl⟩ := hb
  obtain ⟨t, ht0, htle, hteq⟩ := exists_process_eq_shift u hpos hs0
  refine le_trans (sInf_le ⟨t, ⟨ht0, by rw [hteq]; exact hsθ⟩, rfl⟩) ?_
  rw [← ENNReal.ofReal_add (hpos 0).le hs0]
  exact ENNReal.ofReal_le_ofReal htle

omit [NeZero N] [NeZero M] in
theorem state_one_ofStepPath (u : Pressure N M) (ω : ℕ → Step N M) :
    (Trajectory.ofStepPath ω).state u 1 = express (ω 0).1.1 (ω 0).1.2 u := rfl

/-! ### The restart bound -/

/-- **The restart bound.**  If, whatever the first expressed pair `p`, the process started at
the matrix `p` reaches gives the event `E p` probability at most `c`, then the event that the
first holding time lands in `A` and the rest of the realisation lies in `E` of the pair
expressed has probability at most `c`. -/
theorem ctsPathMeasure_restart_le (β : ℝ) (u : Pressure N M) {A : Set ℝ} (hA : MeasurableSet A)
    {E : Jump N M → Set (ℕ → Step N M)} (hE : ∀ p, MeasurableSet (E p)) {c : ℝ≥0∞}
    (hc : ∀ p : Jump N M, ctsPathMeasure β (express p.1 p.2 u) (E p) ≤ c) :
    ctsPathMeasure β u {ω | (ω 0).2 ∈ A ∧ shiftStepPath ω ∈ E (ω 0).1} ≤ c := by
  classical
  set B : Jump N M → Set (Step N M) := fun p =>
    (Prod.fst ⁻¹' {p}) ∩ (Prod.snd ⁻¹' A) with hBdef
  have hBmeas : ∀ p, MeasurableSet (B p) := fun p =>
    (measurable_fst (measurableSet_singleton p)).inter (measurable_snd hA)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Jump N M))) B := by
    intro p _ q _ hpq
    show Disjoint (B p) (B q)
    refine Set.disjoint_left.2 fun z hzp hzq => ?_
    exact absurd ((hzp.1 : z.1 = p).symm.trans (hzq.1 : z.1 = q)) hpq
  have hset : {ω : ℕ → Step N M | (ω 0).2 ∈ A ∧ shiftStepPath ω ∈ E (ω 0).1}
      = ⋃ p ∈ (Finset.univ : Finset (Jump N M)),
          ({ω : ℕ → Step N M | ω 0 ∈ B p} ∩ shiftStepPath ⁻¹' E p) := by
    ext ω
    constructor
    · rintro ⟨h1, h2⟩
      exact Set.mem_biUnion (Finset.mem_univ (ω 0).1) ⟨⟨rfl, h1⟩, h2⟩
    · intro h
      obtain ⟨p, -, ⟨hp1, hp2⟩, hp3⟩ := Set.mem_iUnion₂.1 h
      refine ⟨hp2, ?_⟩
      rw [show (ω 0).1 = p from hp1]
      exact hp3
  rw [hset]
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hterm : ∀ p : Jump N M,
      ctsPathMeasure β u ({ω : ℕ → Step N M | ω 0 ∈ B p} ∩ shiftStepPath ⁻¹' E p)
        ≤ c * stepLaw β u (B p) := by
    intro p
    rw [ctsPathMeasure_restart β u (hBmeas p) (hE p)]
    calc ∫⁻ z in B p, ctsPathMeasure β (express z.1.1 z.1.2 u) (E p) ∂(stepLaw β u)
        ≤ ∫⁻ _ in B p, c ∂(stepLaw β u) := by
          refine lintegral_mono_ae ((ae_restrict_iff' (hBmeas p)).2
            (Filter.Eventually.of_forall fun z hz => ?_))
          rw [show z.1 = p from hz.1]
          exact hc p
      _ = c * stepLaw β u (B p) := setLIntegral_const _ _
  have hsum : ∑ p : Jump N M, stepLaw β u (B p) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj fun p _ => hBmeas p]
    exact prob_le_one
  calc ∑ p : Jump N M,
        ctsPathMeasure β u ({ω : ℕ → Step N M | ω 0 ∈ B p} ∩ shiftStepPath ⁻¹' E p)
      ≤ ∑ p : Jump N M, c * stepLaw β u (B p) := Finset.sum_le_sum fun p _ => hterm p
    _ = c * ∑ p : Jump N M, stepLaw β u (B p) := (Finset.mul_sum _ _ _).symm
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c

/-! ### Equation (19) and Corollary 11 -/

omit [NeZero M] in
theorem isState_zero : IsState (0 : Pressure N M) :=
  ⟨fun _ => by simp [trust], ⟨Classical.arbitrary (Actor N), fun _ => rfl⟩⟩

omit [NeZero M] in
/-- After one expression from the zero matrix the process is in a state, and not at `0`: the
row of the expresser is reset to `0`, but every other row loses `1` on every opinion other than
the one expressed, and there is one of each. -/
theorem express_zero_mem (hM : 2 ≤ M) (hN : 2 ≤ N) (p : Jump N M) :
    express p.1 p.2 (0 : Pressure N M) ∈ (stateSet N M \ {0} : Set (Pressure N M)) := by
  refine ⟨isState_zero.express p.1 p.2, ?_⟩
  intro hzero
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card (Actor N) by simp only [Fintype.card_fin]; omega) p.1
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card (Opinion M) by simp only [Fintype.card_fin]; omega) p.2
  have hval := congrFun (congrFun (hzero : express p.1 p.2 (0 : Pressure N M) = 0) b) q
  rw [express, if_neg hb, if_neg hq] at hval
  simp at hval

/-- The null set on which some holding time fails to be positive. -/
theorem ctsPathMeasure_exists_holdingTime_nonpos (β : ℝ) (u : Pressure N M) :
    ctsPathMeasure β u {ω : ℕ → Step N M | ∃ n, holdingTime n ω ≤ 0} = 0 := by
  rw [show {ω : ℕ → Step N M | ∃ n, holdingTime n ω ≤ 0}
      = ⋃ n, {ω : ℕ → Step N M | holdingTime n ω ≤ 0} from by ext ω; simp]
  exact measure_iUnion_null fun n => ctsPathMeasure_holdingTime_nonpos β u n

end Restart

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

/-- **The bound displayed inside the proof of part 2 of Theorem 2.**  For any `u ∈ S \ {0}`
and any `t > 0`,

```
P (R^{β,u} (L) > t) ≤ 1 - ζ_β^{(M+1)N} + (M+1) N exp (-e^{β/(M-1)} t / ((M+1) N)).
```

**No counterpart among the numbered statements of the paper.**  Theorem 2.2 below --- the Lean
`SocialNetwork.tendsto_hittingTime_ladderSet` --- is the limit this inequality gives at
`t = e^{-β(1-δ)/(M-1)}`, and the inequality itself never becomes a statement.  It is stated
here, out of the paper's order, because Theorem 2.2 is *proved* from it.  Lemma 13 uses
the inequality and not the limit, so it cannot be derived from Theorem 2.2 as stated: taking
the limit has thrown the rate away.  The display is transcribed here so that Lemma 13 has
something to rest on; whether it should be numbered is asked in `FOR-THE-AUTHORS.md`.

It is a step of the paper's own proof of Theorem 2.2, not a citation, and it is **proved**
here, following the argument [GL24] writes out for `M = 2`: split on the greedy event, which
reaches `L` within `(M+1)N` steps by Proposition 7 and costs `1 - ζ_β^{(M+1)N}` by
Proposition 8 and Remark 4; on that event no matrix visited is `0`, so `totalRate` is at least
`e^{β/(M-1)}` and each of the `(M+1)N` holding times is dominated by an exponential of that
rate; `T_{(M+1)N} > t` forces one of them to exceed `t/((M+1)N)`, and a union bound finishes.
It inherits `sorryAx` from Proposition 7 and from nothing else. -/
theorem probHittingGT_ladderSet_le_of_ne_zero (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {u : Pressure N M} (hu : IsState u) (hu0 : u ≠ 0) {t : ℝ} (ht : 0 < t) :
    probHittingGT β u (ladderSet N M) (ENNReal.ofReal t)
      ≤ ENNReal.ofReal (1 - zeta N M β ^ ((M + 1) * N)
          + (((M + 1) * N : ℕ) : ℝ) *
            Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * t) / (((M + 1) * N : ℕ) : ℝ))) := by
  have hN2 : 2 ≤ N := by omega
  set K : ℕ := (M + 1) * N with hKdef
  have hK0 : K ≠ 0 := by simp only [hKdef]; positivity
  have hKr : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hK0
  set r : ℝ := Real.exp (β / ((M : ℝ) - 1)) with hrdef
  have hrpos : 0 < r := Real.exp_pos _
  -- the holding times are almost surely positive
  set Z : Set (ℕ → Step N M) := {ω | ∃ n, holdingTime n ω ≤ 0} with hZdef
  have hZnull : ctsPathMeasure β u Z = 0 := by
    have hcover : Z = ⋃ n, {ω : ℕ → Step N M | holdingTime n ω ≤ 0} := by
      ext ω; simp [hZdef]
    rw [hcover]
    exact measure_iUnion_null fun n => ctsPathMeasure_holdingTime_nonpos β u n
  -- either the run is not greedy, or some holding time vanishes, or `T_K` exceeds `t`
  have hsub : {ω : ℕ → Step N M | ENNReal.ofReal t < hittingTimeCts u (ladderSet N M) ω}
      ⊆ ((ctsGreedyEvents u K)ᶜ ∪ Z)
        ∪ (ctsGreedyEvents u K ∩ {ω | t < jumpTime K ω}) := by
    intro ω hω
    by_cases hg : ω ∈ ctsGreedyEvents u K
    · by_cases hz : ω ∈ Z
      · exact Or.inl (Or.inr hz)
      · refine Or.inr ⟨hg, ?_⟩
        have hpos : ∀ n, 0 < holdingTime n ω := fun n => by
          by_contra hcon
          exact hz ⟨n, not_lt.1 hcon⟩
        have hmem : (Trajectory.ofStepPath ω).state u K ∈ ladderSet N M :=
          isLadder_state_of_greedy (Trajectory.ofStepPath ω) hM hN hu fun k hk => hg k hk
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).1
          (lt_of_lt_of_le hω (hittingTimeCts_le_jumpTime hpos hK0 hmem))
    · exact Or.inl (Or.inl hg)
  -- the greedy event
  have hzle : zeta N M β ^ K ≤ 1 :=
    pow_le_one₀ (zeta_pos N M β).le (zeta_le_one N M β)
  have h1 : ctsPathMeasure β u ((ctsGreedyEvents u K)ᶜ ∪ Z)
      ≤ ENNReal.ofReal (1 - zeta N M β ^ K) := by
    refine le_trans (measure_union_le _ _) ?_
    rw [hZnull, add_zero, prob_compl_eq_one_sub (measurableSet_ctsGreedyEvents u K)]
    have hge : ENNReal.ofReal (zeta N M β ^ K) ≤ ctsPathMeasure β u (ctsGreedyEvents u K) := by
      rw [ENNReal.ofReal_pow (zeta_pos N M β).le]
      exact zeta_pow_le_ctsPathMeasure_greedyEvents hM hβ K
    rw [ENNReal.ofReal_sub _ (pow_nonneg (zeta_pos N M β).le K), ENNReal.ofReal_one]
    exact tsub_le_tsub_left hge 1
  -- the clock
  have h2 : ctsPathMeasure β u (ctsGreedyEvents u K ∩ {ω | t < jumpTime K ω})
      ≤ ENNReal.ofReal ((K : ℝ) * Real.exp (-(r * t) / (K : ℝ))) := by
    have hcover : ctsGreedyEvents u K ∩ {ω : ℕ → Step N M | t < jumpTime K ω}
        ⊆ ⋃ n ∈ Finset.range K,
            (ctsGreedyEvents u n ∩ {ω : ℕ → Step N M | t / (K : ℝ) < holdingTime n ω}) := by
      rintro ω ⟨hg, hj⟩
      have hsum : ∑ _n ∈ Finset.range K, t / (K : ℝ)
          < ∑ n ∈ Finset.range K, holdingTime n ω := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [mul_div_cancel₀ _ hKr.ne']
        exact hj
      obtain ⟨n, hn, hlt⟩ := Finset.exists_lt_of_sum_lt hsum
      exact Set.mem_biUnion hn
        ⟨fun k hk => hg k (lt_trans hk (Finset.mem_range.1 hn)), hlt⟩
    refine le_trans (measure_mono hcover) ?_
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hbound : ∀ n ∈ Finset.range K,
        ctsPathMeasure β u
            (ctsGreedyEvents u n ∩ {ω : ℕ → Step N M | t / (K : ℝ) < holdingTime n ω})
          ≤ ENNReal.ofReal (Real.exp (-(r * (t / (K : ℝ))))) := fun n _ =>
      ctsPathMeasure_greedy_holdingTime_gt hM hN2 hβ hu hu0 n (by positivity)
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : -(r * (t / (K : ℝ))) = -(r * t) / (K : ℝ) := by field_simp
    rw [this]
  -- putting the two together
  refine le_trans (le_trans (measure_mono hsub) (measure_union_le _ _)) ?_
  refine le_trans (add_le_add h1 h2) ?_
  rw [← ENNReal.ofReal_add (by linarith) (by positivity)]

/-- **Theorem 2.2.** For every fixed `δ > 0`,

```
sup_{u ∈ S \ {0}} P (R^{β,u} (L) > e^{-β(1-δ)/(M-1)})  →  0   as β → +∞.
```

The zero matrix has to be excluded: from `0` every rate equals `1`, so the first expression
takes a time of order `1` rather than `e^{-β/(M-1)}`.  Corollary 11 is the version that covers
it, at the price of an extra exponential random variable.

Unlike Theorem 2.1 this does not mention `μ^β`, and so does not wait on the existence of one.
**Proved** from the display above at `t = e^{-β(1-δ)/(M-1)}`, where
`e^{β/(M-1)} t = e^{βδ/(M-1)} → ∞` kills the second term and Remark 4 kills the first; it
inherits `sorryAx` from that display, hence from Proposition 7, and from nothing else. -/
theorem tendsto_hittingTime_ladderSet (hM : 2 ≤ M) (hN : 3 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun β : ℝ => ⨆ u ∈ (stateSet N M \ {0} : Set (Pressure N M)),
        probHittingGT β u (ladderSet N M)
          (ENNReal.ofReal (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))))
      Filter.atTop (nhds 0) := by
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hKpos : (0 : ℝ) < (((M + 1) * N : ℕ) : ℝ) := by push_cast; nlinarith
  set b : ℝ → ℝ := fun β =>
    1 - zeta N M β ^ ((M + 1) * N)
      + (((M + 1) * N : ℕ) : ℝ) *
        Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) *
          Real.exp (-β / ((M : ℝ) - 1) * (1 - δ))) / (((M + 1) * N : ℕ) : ℝ)) with hbdef
  have key : ∀ β : ℝ, 0 ≤ β →
      (⨆ u ∈ (stateSet N M \ {0} : Set (Pressure N M)),
        probHittingGT β u (ladderSet N M)
          (ENNReal.ofReal (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))))
        ≤ ENNReal.ofReal (b β) := by
    intro β hβ
    refine iSup₂_le fun u hu => ?_
    exact probHittingGT_ladderSet_le_of_ne_zero hM hN hβ hu.1
      (by simpa using hu.2) (Real.exp_pos _)
  -- the bound tends to zero
  have hb : Filter.Tendsto b Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun β : ℝ => 1 - zeta N M β ^ ((M + 1) * N))
        Filter.atTop (nhds 0) := by
      have hle : ∀ β : ℝ, 1 - zeta N M β ^ ((M + 1) * N)
          ≤ (((M + 1) * N : ℕ) : ℝ) *
            ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))) := by
        intro β
        have := one_sub_le_zeta_pow N M β ((M + 1) * N)
        linarith
      have hnn : ∀ β : ℝ, 0 ≤ 1 - zeta N M β ^ ((M + 1) * N) := by
        intro β
        have h := pow_le_one₀ (zeta_pos N M β).le (zeta_le_one N M β) (n := (M + 1) * N)
        linarith
      have hright : Filter.Tendsto
          (fun β : ℝ => (((M + 1) * N : ℕ) : ℝ) *
            ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))))
          Filter.atTop (nhds 0) := by
        have hdiv : Filter.Tendsto (fun β : ℝ => -(β / ((M : ℝ) - 1)))
            Filter.atTop Filter.atBot :=
          Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.atTop_div_const hM1)
        have := Real.tendsto_exp_atBot.comp hdiv
        simpa [mul_assoc] using this.const_mul ((((M + 1) * N : ℕ) : ℝ) * ((M : ℝ) * (N : ℝ)))
      exact squeeze_zero hnn hle (by simpa [mul_assoc] using hright)
    have h2 : Filter.Tendsto
        (fun β : ℝ => (((M + 1) * N : ℕ) : ℝ) *
          Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) *
            Real.exp (-β / ((M : ℝ) - 1) * (1 - δ))) / (((M + 1) * N : ℕ) : ℝ)))
        Filter.atTop (nhds 0) := by
      have hin : ∀ β : ℝ, Real.exp (β / ((M : ℝ) - 1)) *
          Real.exp (-(β / ((M : ℝ) - 1) * (1 - δ))) = Real.exp (β / ((M : ℝ) - 1) * δ) := by
        intro β
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
      have hgrow : Filter.Tendsto (fun β : ℝ => Real.exp (β / ((M : ℝ) - 1) * δ))
          Filter.atTop Filter.atTop :=
        Real.tendsto_exp_atTop.comp
          ((Filter.tendsto_id.atTop_div_const hM1).atTop_mul_const hδ)
      have hneg : Filter.Tendsto
          (fun β : ℝ => -Real.exp (β / ((M : ℝ) - 1) * δ) / (((M + 1) * N : ℕ) : ℝ))
          Filter.atTop Filter.atBot :=
        (Filter.tendsto_neg_atTop_atBot.comp hgrow).atBot_div_const hKpos
      have := (Real.tendsto_exp_atBot.comp hneg).const_mul
        ((((M + 1) * N : ℕ) : ℝ))
      simp only [Function.comp_def, mul_zero] at this
      simpa [hin, neg_div] using this
    simpa [hbdef] using h1.add h2
  have hbE : Filter.Tendsto (fun β : ℝ => ENNReal.ofReal (b β)) Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbE
    (Filter.Eventually.of_forall fun _ => by simp) ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with β hβ using key β hβ

/-- **Corollary 11.** For every fixed `δ > 0`,

```
P (R^{β,0} (L) > τ + e^{-β(1-δ)/(M-1)})  →  0   as β → +∞,
```

with `τ` exponentially distributed of mean `1/(MN)` and independent of the process that
follows it.

Theorem 2.2 again, after the waiting time that is why Theorem 2.2 excludes the zero matrix:
every rate at `0` equals `1`, and the first expression lands on a state that is not `0`.

`τ` is the process's **own first jump time** `T₁`, and that is the reading the paper's proof
uses.  From `0` it is exponential of mean `1/(MN)` by `totalRate_zero`, and the paper's clause
"independent from `(U_t^{β,u})_t`" is independence from the process *after* the jump, `u`
being the state it lands on; that is what equation (19) below decomposes.

Read the other way — `τ` an independent copy, and independent of `R^{β,0}(L)` itself — the
corollary is **false**: `R^{β,0}(L) = T₁ + o(1)` in probability, so the left-hand side tends to
`P (T₁ > τ)` with `T₁` and `τ` independent and both exponential of rate `MN`, which is `1/2`.

An earlier version of this statement rendered the independence as a supremum over `s ≥ 0`
weighted by `e^{-MNs}`, which at `s = 0` leaves `P (R^{β,0} (L) > e^{-β(1-δ)/(M-1)})` standing
alone and tends to `1`.  That was an error of this formalisation, not of the paper; see the
blueprint node `cor11` and `FOR-THE-AUTHORS.md` §2.11. -/
theorem tendsto_hittingTime_ladderSet_zero (hM : 2 ≤ M) (hN : 3 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun β : ℝ => probHittingGTAfterFirstJump β 0 (ladderSet N M)
        (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ))))
      Filter.atTop (nhds 0) := by
  classical
  have key : ∀ β : ℝ, probHittingGTAfterFirstJump β 0 (ladderSet N M)
        (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))
      ≤ ⨆ v ∈ (stateSet N M \ {0} : Set (Pressure N M)),
          probHittingGT β v (ladderSet N M)
            (ENNReal.ofReal (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))) := by
    intro β
    set t := Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)) with htdef
    have htpos : 0 < t := Real.exp_pos _
    set E : Jump N M → Set (ℕ → Step N M) := fun p =>
      {ω | ENNReal.ofReal t < hittingTimeCts (express p.1 p.2 (0 : Pressure N M))
        (ladderSet N M) ω} with hEdef
    have hEmeas : ∀ p, MeasurableSet (E p) := fun p =>
      (measurable_hittingTimeCts _ _) measurableSet_Ioi
    have hc : ∀ p : Jump N M,
        ctsPathMeasure β (express p.1 p.2 (0 : Pressure N M)) (E p)
          ≤ ⨆ v ∈ (stateSet N M \ {0} : Set (Pressure N M)),
              probHittingGT β v (ladderSet N M) (ENNReal.ofReal t) := fun p =>
      le_iSup₂_of_le (express p.1 p.2 (0 : Pressure N M))
        (express_zero_mem hM (by omega) p) le_rfl
    have hsub : {ω : ℕ → Step N M |
          ENNReal.ofReal (jumpTime 1 ω + t) < hittingTimeCts 0 (ladderSet N M) ω}
        ⊆ {ω : ℕ → Step N M | ∃ n, holdingTime n ω ≤ 0}
          ∪ {ω : ℕ → Step N M | (ω 0).2 ∈ (Set.univ : Set ℝ)
              ∧ shiftStepPath ω ∈ E (ω 0).1} := by
      intro ω hω
      by_cases hz : ∃ n, holdingTime n ω ≤ 0
      · exact Or.inl hz
      refine Or.inr ⟨Set.mem_univ _, ?_⟩
      have hpos : ∀ n, 0 < holdingTime n ω := fun n => not_le.1 fun h => hz ⟨n, h⟩
      have hle := hittingTimeCts_le_shift (0 : Pressure N M) (ladderSet N M) hpos
      rw [state_one_ofStepPath] at hle
      have hT1 : jumpTime 1 ω = holdingTime 0 ω := by simp [jumpTime]
      have h4 : ENNReal.ofReal (jumpTime 1 ω + t)
          = ENNReal.ofReal (holdingTime 0 ω) + ENNReal.ofReal t := by
        rw [hT1, ENNReal.ofReal_add (hpos 0).le htpos.le]
      have hω' : ENNReal.ofReal (jumpTime 1 ω + t) < hittingTimeCts 0 (ladderSet N M) ω := hω
      rw [h4] at hω'
      exact (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).1 (lt_of_lt_of_le hω' hle)
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [ctsPathMeasure_exists_holdingTime_nonpos, zero_add]
    exact ctsPathMeasure_restart_le β 0 MeasurableSet.univ hEmeas hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_hittingTime_ladderSet hM hN hδ)
    (Filter.Eventually.of_forall fun _ => by simp)
    (Filter.Eventually.of_forall key)

/-- **The display behind Remark 6**, and the same estimate as the one behind part 2 of
Theorem 2, with `L` replaced by `L^o` and the horizon `(M+1)N` by `N`.

From a consensus state for `o`, `N` greedy expressions land on a ladder supporting `o` and
none of the states passed through leaves `C^o`.  So on the greedy event, and as soon as the
holding times are positive, `R^{β,u} (L^o) ≤ T_N < R^{β,u} (C^{-o})`, and the only way to fail
is for `T_N` to reach `t`.  Proposition 8 bounds the first escape, the exponential race of the
holding times the second. -/
theorem le_probHittingLadderFirst (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {u : Pressure N M} (hu : IsConsensus o u) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (zeta N M β ^ N
        - (N : ℝ) * Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) * t) / (N : ℝ)))
      ≤ probHittingLadderFirst β o u (ENNReal.ofReal t) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set r : ℝ := Real.exp (β / ((M : ℝ) - 1)) with hrdef
  have hrpos : 0 < r := Real.exp_pos _
  set Z : Set (ℕ → Step N M) := {ω | ∃ n, holdingTime n ω ≤ 0} with hZdef
  have hZnull : ctsPathMeasure β u Z = 0 := ctsPathMeasure_exists_holdingTime_nonpos β u
  have hsub : {ω : ℕ → Step N M | hittingTimeCts u {v : Pressure N M | IsLadder o v} ω
        < min (ENNReal.ofReal t) (hittingTimeCts u (consensusSetOther N o) ω)}ᶜ
      ⊆ ((ctsGreedyEvents u N)ᶜ ∪ Z)
        ∪ (ctsGreedyEvents u N ∩ {ω | t ≤ jumpTime N ω}) := by
    intro ω hω
    by_cases hg : ω ∈ ctsGreedyEvents u N
    · by_cases hz : ω ∈ Z
      · exact Or.inl (Or.inr hz)
      · refine Or.inr ⟨hg, ?_⟩
        have hpos : ∀ n, 0 < holdingTime n ω := fun n => by
          by_contra hcon
          exact hz ⟨n, not_lt.1 hcon⟩
        have hmemL : (Trajectory.ofStepPath ω).state u N ∈ {v : Pressure N M | IsLadder o v} :=
          isLadder_state (Trajectory.ofStepPath ω) hM hN2 hu fun k hk => hg k hk
        have hR1 : hittingTimeCts u {v : Pressure N M | IsLadder o v} ω
            ≤ ENNReal.ofReal (jumpTime N ω) :=
          hittingTimeCts_le_jumpTime hpos (by omega) hmemL
        have hR2 : ENNReal.ofReal (jumpTime N ω)
            < hittingTimeCts u (consensusSetOther N o) ω :=
          jumpTime_lt_hittingTimeCts hpos fun n hn =>
            (isConsensus_state (Trajectory.ofStepPath ω) hM hN2 hu
              (fun k hk => hg k hk) n hn).notMem_consensusSetOther
        by_contra hcon
        exact hω (lt_min (lt_of_le_of_lt hR1
          ((ENNReal.ofReal_lt_ofReal_iff ht).2 (not_le.1 hcon)))
          (lt_of_le_of_lt hR1 hR2))
    · exact Or.inl (Or.inl hg)
  have h1 : ctsPathMeasure β u ((ctsGreedyEvents u N)ᶜ ∪ Z)
      ≤ ENNReal.ofReal (1 - zeta N M β ^ N) := by
    refine le_trans (measure_union_le _ _) ?_
    rw [hZnull, add_zero, prob_compl_eq_one_sub (measurableSet_ctsGreedyEvents u N)]
    have hge : ENNReal.ofReal (zeta N M β ^ N) ≤ ctsPathMeasure β u (ctsGreedyEvents u N) := by
      rw [ENNReal.ofReal_pow (zeta_pos N M β).le]
      exact zeta_pow_le_ctsPathMeasure_greedyEvents hM hβ N
    rw [ENNReal.ofReal_sub _ (pow_nonneg (zeta_pos N M β).le N), ENNReal.ofReal_one]
    exact tsub_le_tsub_left hge 1
  have h2 : ctsPathMeasure β u (ctsGreedyEvents u N ∩ {ω | t ≤ jumpTime N ω})
      ≤ ENNReal.ofReal ((N : ℝ) * Real.exp (-(r * t) / (N : ℝ))) := by
    have hcover : ctsGreedyEvents u N ∩ {ω : ℕ → Step N M | t ≤ jumpTime N ω}
        ⊆ ⋃ n ∈ Finset.range N,
            (ctsGreedyEvents u n ∩ {ω : ℕ → Step N M | t / (N : ℝ) ≤ holdingTime n ω}) := by
      rintro ω ⟨hg, hj⟩
      have hsum : ∑ _n ∈ Finset.range N, t / (N : ℝ)
          ≤ ∑ n ∈ Finset.range N, holdingTime n ω := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hNr.ne']
        exact hj
      obtain ⟨n, hn, hle⟩ :=
        Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.2 (by omega)) hsum
      exact Set.mem_biUnion hn
        ⟨fun k hk => hg k (lt_trans hk (Finset.mem_range.1 hn)), hle⟩
    refine le_trans (measure_mono hcover) ?_
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hbound : ∀ n ∈ Finset.range N,
        ctsPathMeasure β u
            (ctsGreedyEvents u n ∩ {ω : ℕ → Step N M | t / (N : ℝ) ≤ holdingTime n ω})
          ≤ ENNReal.ofReal (Real.exp (-(r * (t / (N : ℝ))))) := fun n _ =>
      ctsPathMeasure_greedy_holdingTime_ge hM hN2 hβ hu.isState hu.ne_zero n (by positivity)
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdiv : -(r * (t / (N : ℝ))) = -(r * t) / (N : ℝ) := by field_simp
    rw [hdiv]
  have hzle : zeta N M β ^ N ≤ 1 := pow_le_one₀ (zeta_pos N M β).le (zeta_le_one N M β)
  have hbad : ctsPathMeasure β u {ω : ℕ → Step N M |
        hittingTimeCts u {v : Pressure N M | IsLadder o v} ω
          < min (ENNReal.ofReal t) (hittingTimeCts u (consensusSetOther N o) ω)}ᶜ
      ≤ ENNReal.ofReal (1 - zeta N M β ^ N
          + (N : ℝ) * Real.exp (-(r * t) / (N : ℝ))) := by
    refine le_trans (le_trans (measure_mono hsub) (measure_union_le _ _)) ?_
    refine le_trans (add_le_add h1 h2) ?_
    rw [← ENNReal.ofReal_add (by linarith) (by positivity)]
  have hcompl : probHittingLadderFirst β o u (ENNReal.ofReal t)
      = 1 - ctsPathMeasure β u {ω : ℕ → Step N M |
        hittingTimeCts u {v : Pressure N M | IsLadder o v} ω
          < min (ENNReal.ofReal t) (hittingTimeCts u (consensusSetOther N o) ω)}ᶜ := by
    have h := prob_compl_eq_one_sub (μ := ctsPathMeasure β u)
      (measurableSet_hittingLadderFirst o u (ENNReal.ofReal t)).compl
    rwa [compl_compl] at h
  have hrw : zeta N M β ^ N - (N : ℝ) * Real.exp (-(r * t) / (N : ℝ))
      = 1 - (1 - zeta N M β ^ N + (N : ℝ) * Real.exp (-(r * t) / (N : ℝ))) := by ring
  rw [hcompl, hrw, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  exact tsub_le_tsub_left hbad 1

/-- **Remark 6.** For every fixed `o` and `δ > 0`,

```
inf_{u ∈ C^o} P (R^{β,u} (L^o) < min {e^{-β(1-δ)/(M-1)}, R^{β,u} (C^{-o})})  →  1
```

as `β → +∞`: from anywhere in the consensus set for `o`, the process reaches a ladder
supporting `o` --- not merely some ladder --- before `e^{-β(1-δ)/(M-1)}` and before it can
agree on any other opinion.

The paper states it as a consequence of its note that the first term on the right of
equation (14) may be replaced by `P (R^{β,u}(L) > t, R^{β,u}(L^o) < R^{β,u}(C^{-o}))`, "by
following the same steps of the proof of part 2 of Theorem 2".  It is those steps, at the
horizon `N` rather than `(M+1)N`, which is the whole difference: from a consensus state the
greedy run needs only the *last* stage of Proposition 7, and that stage lands on `L^o` and
passes through `C^o` alone.  Continuing to `(M+1)N` would leave `L^o` again, so the horizon
has to be `N` here. -/
theorem tendsto_probHittingLadderFirst (hM : 2 ≤ M) (hN : 3 ≤ N) {δ : ℝ} (hδ : 0 < δ)
    (o : Opinion M) :
    Filter.Tendsto
      (fun β : ℝ => ⨅ u ∈ consensusSet N o, probHittingLadderFirst β o u
        (ENNReal.ofReal (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))))
      Filter.atTop (nhds 1) := by
  have hN2 : 2 ≤ N := by omega
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  set b : ℝ → ℝ := fun β =>
    1 - zeta N M β ^ N
      + (N : ℝ) * Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) *
          Real.exp (-β / ((M : ℝ) - 1) * (1 - δ))) / (N : ℝ)) with hbdef
  have key : ∀ β : ℝ, 0 ≤ β →
      ENNReal.ofReal (1 - b β)
        ≤ ⨅ u ∈ consensusSet N o, probHittingLadderFirst β o u
            (ENNReal.ofReal (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))) := by
    intro β hβ
    refine le_iInf₂ fun u hu => ?_
    have h := le_probHittingLadderFirst hM hN hβ hu
      (Real.exp_pos (-β / ((M : ℝ) - 1) * (1 - δ)))
    refine le_trans (le_of_eq (congrArg ENNReal.ofReal ?_)) h
    rw [hbdef]
    ring
  have hb : Filter.Tendsto b Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun β : ℝ => 1 - zeta N M β ^ N) Filter.atTop (nhds 0) := by
      have hle : ∀ β : ℝ, 1 - zeta N M β ^ N
          ≤ (N : ℝ) * ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))) := by
        intro β
        have := one_sub_le_zeta_pow N M β N
        linarith
      have hnn : ∀ β : ℝ, 0 ≤ 1 - zeta N M β ^ N := by
        intro β
        have h := pow_le_one₀ (zeta_pos N M β).le (zeta_le_one N M β) (n := N)
        linarith
      have hright : Filter.Tendsto
          (fun β : ℝ => (N : ℝ) * ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))))
          Filter.atTop (nhds 0) := by
        have hdiv : Filter.Tendsto (fun β : ℝ => -(β / ((M : ℝ) - 1)))
            Filter.atTop Filter.atBot :=
          Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.atTop_div_const hM1)
        have := Real.tendsto_exp_atBot.comp hdiv
        simpa [mul_assoc] using this.const_mul ((N : ℝ) * ((M : ℝ) * (N : ℝ)))
      exact squeeze_zero hnn hle (by simpa [mul_assoc] using hright)
    have h2 : Filter.Tendsto
        (fun β : ℝ => (N : ℝ) * Real.exp (-(Real.exp (β / ((M : ℝ) - 1)) *
          Real.exp (-β / ((M : ℝ) - 1) * (1 - δ))) / (N : ℝ)))
        Filter.atTop (nhds 0) := by
      have hin : ∀ β : ℝ, Real.exp (β / ((M : ℝ) - 1)) *
          Real.exp (-(β / ((M : ℝ) - 1) * (1 - δ))) = Real.exp (β / ((M : ℝ) - 1) * δ) := by
        intro β
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
      have hgrow : Filter.Tendsto (fun β : ℝ => Real.exp (β / ((M : ℝ) - 1) * δ))
          Filter.atTop Filter.atTop :=
        Real.tendsto_exp_atTop.comp
          ((Filter.tendsto_id.atTop_div_const hM1).atTop_mul_const hδ)
      have hneg : Filter.Tendsto
          (fun β : ℝ => -Real.exp (β / ((M : ℝ) - 1) * δ) / (N : ℝ))
          Filter.atTop Filter.atBot :=
        (Filter.tendsto_neg_atTop_atBot.comp hgrow).atBot_div_const hNr
      have := (Real.tendsto_exp_atBot.comp hneg).const_mul (N : ℝ)
      simp only [Function.comp_def, mul_zero] at this
      simpa [hin, neg_div] using this
    simpa [hbdef] using h1.add h2
  have hbE : Filter.Tendsto (fun β : ℝ => ENNReal.ofReal (1 - b β)) Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun β : ℝ => 1 - b β) Filter.atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hb
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 1).comp h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hbE tendsto_const_nhds ?_
    (Filter.Eventually.of_forall fun β => ?_)
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with β hβ using key β hβ
  · exact iInf₂_le_of_le (ladderOf N o) ((isLadder_ladderOf o).isConsensus hM hN2) prob_le_one

/-- **Equation (19)**, the quantitative form of Corollary 11:

```
P (R^{β,0} (L) > 2β) ≤ P (τ > β) + sup_{u ≠ 0} P (R^{β,u} (L) > β),
```

with `τ` the waiting time before the first expression from the zero matrix.

**No counterpart among the numbered statements of the paper.**  Corollary 11 above --- the Lean
`SocialNetwork.tendsto_hittingTime_ladderSet_zero` --- is a limit, and this is the inequality
its proof gives; Lemma 13 uses the inequality.  The paper attributes equation (19) to
Corollary 11, but what it decomposes is Corollary 11's *proof*: the waiting time at `0`, then
Theorem 2.2.

`P (τ > β)` is written here as the paper evaluates it, `e^{-β/(MN)}`.  Note that `τ` is
declared exponential of mean `1/(MN)` — and is, by `totalRate_zero` — for which
`P (τ > β) = e^{-MNβ}`; since
`e^{-MNβ} ≤ e^{-β/(MN)}` for `β ≥ 0`, the form written here is the weaker of the two, so
Lemma 13 follows from either reading. -/
theorem probHittingGT_ladderSet_zero_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    probHittingGT β 0 (ladderSet N M) (ENNReal.ofReal (2 * β))
      ≤ ENNReal.ofReal (Real.exp (-β / ((M * N : ℕ) : ℝ)))
        + ⨆ v ∈ (stateSet N M \ {0} : Set (Pressure N M)),
            probHittingGT β v (ladderSet N M) (ENNReal.ofReal β) := by
  classical
  have hMN1 : 1 ≤ M * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hMNone : (1 : ℝ) ≤ ((M * N : ℕ) : ℝ) := by exact_mod_cast hMN1
  have hMNpos : (0 : ℝ) < ((M * N : ℕ) : ℝ) := by linarith
  set E : Jump N M → Set (ℕ → Step N M) := fun p =>
    {ω | ENNReal.ofReal β < hittingTimeCts (express p.1 p.2 (0 : Pressure N M))
      (ladderSet N M) ω} with hEdef
  have hEmeas : ∀ p, MeasurableSet (E p) := fun p =>
    (measurable_hittingTimeCts _ _) measurableSet_Ioi
  have hc : ∀ p : Jump N M,
      ctsPathMeasure β (express p.1 p.2 (0 : Pressure N M)) (E p)
        ≤ ⨆ v ∈ (stateSet N M \ {0} : Set (Pressure N M)),
            probHittingGT β v (ladderSet N M) (ENNReal.ofReal β) := fun p =>
    le_iSup₂_of_le (express p.1 p.2 (0 : Pressure N M))
      (express_zero_mem hM (by omega) p) le_rfl
  have hW : ctsPathMeasure β 0 {ω : ℕ → Step N M | holdingTime 0 ω ∈ Set.Ioi β}
      = ENNReal.ofReal (Real.exp (-(((M * N : ℕ) : ℝ) * β))) := by
    rw [ctsPathMeasure_holdingTime_zero β 0 measurableSet_Ioi, totalRate_zero,
      expMeasure_Ioi_of_nonneg hMNpos hβ]
  have hsub : {ω : ℕ → Step N M | ENNReal.ofReal (2 * β) < hittingTimeCts 0 (ladderSet N M) ω}
      ⊆ {ω : ℕ → Step N M | ∃ n, holdingTime n ω ≤ 0}
        ∪ ({ω : ℕ → Step N M | holdingTime 0 ω ∈ Set.Ioi β}
          ∪ {ω : ℕ → Step N M | (ω 0).2 ∈ Set.Iic β ∧ shiftStepPath ω ∈ E (ω 0).1}) := by
    intro ω hω
    by_cases hz : ∃ n, holdingTime n ω ≤ 0
    · exact Or.inl hz
    refine Or.inr ?_
    have hpos : ∀ n, 0 < holdingTime n ω := fun n => not_le.1 fun h => hz ⟨n, h⟩
    by_cases hw : β < holdingTime 0 ω
    · exact Or.inl hw
    refine Or.inr ⟨not_lt.1 hw, ?_⟩
    have hle := hittingTimeCts_le_shift (0 : Pressure N M) (ladderSet N M) hpos
    rw [state_one_ofStepPath] at hle
    have h1 := lt_of_lt_of_le hω hle
    have h2 : ENNReal.ofReal (holdingTime 0 ω) ≤ ENNReal.ofReal β :=
      ENNReal.ofReal_le_ofReal (not_lt.1 hw)
    have h4 : ENNReal.ofReal β + ENNReal.ofReal β = ENNReal.ofReal (2 * β) := by
      rw [← ENNReal.ofReal_add hβ hβ]; ring_nf
    have h3 : ENNReal.ofReal β + ENNReal.ofReal β
        < ENNReal.ofReal β
          + hittingTimeCts (express (ω 0).1.1 (ω 0).1.2 0) (ladderSet N M)
              (shiftStepPath ω) := by
      rw [h4]
      exact lt_of_lt_of_le h1 (add_le_add h2 (le_refl _))
    exact (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).1 h3
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [ctsPathMeasure_exists_holdingTime_nonpos, zero_add]
  refine le_trans (measure_union_le _ _) ?_
  rw [hW]
  refine add_le_add ?_ (ctsPathMeasure_restart_le β 0 measurableSet_Iic hEmeas hc)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [neg_div, neg_le_neg_iff]
  have h1 : β / ((M * N : ℕ) : ℝ) ≤ β := div_le_self hβ hMNone
  have h2 : β ≤ ((M * N : ℕ) : ℝ) * β := le_mul_of_one_le_left hβ hMNone
  linarith

omit [NeZero N] [NeZero M] in
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

omit [NeZero N] [NeZero M] in
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

omit [NeZero N] [NeZero M] in
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
