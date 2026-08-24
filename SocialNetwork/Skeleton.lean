/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Consensus
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The skeleton process (Definition 3)

Definition 3 of arXiv:2607.19651 introduces the *skeleton* `Ũ_n^{β,u} := U_{T_n}^{β,u}`, the
discrete-time chain obtained from the Markov jump process by forgetting the holding times.  This
file builds it.

## What is built here

The generator of equation (3) is

```
G f (u) = ∑_{o ∈ O} ∑_{a ∈ A} exp (β u (a, o)) [f (π^{a,o} (u)) - f (u)],
```

so the jump rate of the pair `(a, o)` at the matrix `u` is `exp (β u (a, o))`, with no
normalisation.  The embedded chain therefore picks the pair `(a, o)` with probability
proportional to that rate.  In the scaled coordinates of `SocialNetwork.Defs`, where
`v (a, o) = (M - 1) * u (a, o)`, the rate reads `exp (β * v (a, o) / (M - 1))`; this is
`SocialNetwork.jumpRate`.

Two chains are built, and they are the same chain seen through two lenses.

* `SocialNetwork.skeletonKernel β : Kernel (Pressure N M) (Pressure N M)` is the paper's
  `Ũ^{β,u}` literally: a transition kernel on pressure matrices.
* `SocialNetwork.pathMeasure β u` is the law of the driving sequence `(Aₙ, Oₙ)ₙ` itself, built
  by Ionescu-Tulcea from a family of kernels indexed by the past.  Its sample space is
  `ℕ → Jump N M`, which is a `SocialNetwork.Trajectory` under `Trajectory.ofPath`, so the
  deterministic results of `SocialNetwork.Trajectory` and `SocialNetwork.Consensus` apply to a
  realisation *pointwise*, with no almost-sure qualifier anywhere.  That is the whole point of
  driving the chain by the pairs rather than by the states: the state at time `n` is
  `Trajectory.state u n` by definition, not up to a null set.

`SocialNetwork.map_drivingKernel` records that the two agree in one step.

## Measurability is free

`Pressure N M = Actor N → Opinion M → ℤ` is countable with measurable singletons, hence a
`DiscreteMeasurableSpace`: *every* subset is measurable and *every* function out of it is
measurable.  The same holds for `Jump N M` and for every space of finite histories.  So no
σ-algebra is ever constructed by hand below; `MeasurableSet.of_discrete` and
`Measurable.of_discrete` do all the work.

## Main definitions

* `SocialNetwork.jumpRate` — the rate of equation (3), in scaled coordinates.
* `SocialNetwork.jumpPMF` — the law of the pair `(Aₙ, Oₙ)` given the current matrix.
* `SocialNetwork.skeletonKernel` — Definition 3, as a `Kernel (Pressure N M) (Pressure N M)`.
* `SocialNetwork.drivingKernel`, `SocialNetwork.pathMeasure` — the same chain driven by the
  pairs, and its law on trajectories, via `ProbabilityTheory.Kernel.traj`.
* `SocialNetwork.skeleton`, `SocialNetwork.returnTime` — the process `Ũ_n^{β,u}` and the
  return time `R̃^{β,u} (θ)` of Definition 3.
* `SocialNetwork.greedyEvent`, `SocialNetwork.greedyEvents` — the paper's `ξₙ^u` and
  `⋂_{j ≤ n} ξⱼ^u`, as subsets of the sample space.
* `SocialNetwork.entrySup`, `SocialNetwork.argmaxFinset` — the paper's `y (v)` and `Y (v)`.
* `SocialNetwork.zeta` — the constant `ζ_β` of Proposition 8.

## Main results

* `SocialNetwork.isMarkovKernel_skeletonKernel` — `Ũ^{β,u}` is a Markov kernel.
* `SocialNetwork.skeletonKernel_reachable` — the kernel is carried by the matrices reachable
  from `v` by a single `express`.
* `SocialNetwork.isState_skeletonKernel` — the state space `S` is preserved with probability
  one, which is `SocialNetwork.Trajectory.isState_state` read one step at a time.
* `SocialNetwork.measurableSet_greedyEvent` — `ξₙ^u` is measurable, being a cylinder.
* `SocialNetwork.entry_mem_of_mem_greedyEvents` — Proposition 6 on the greedy event.
* `SocialNetwork.isLadder_state_of_mem_greedyEvents` — the last step of Proposition 7 on the
  greedy event.
* `SocialNetwork.le_entrySup_sub_one` — the gap estimate behind Proposition 8.
* `SocialNetwork.one_sub_le_zeta_pow` — Remark 4, Bernoulli's inequality for `ζ_β`.
* `SocialNetwork.zeta_le_jumpPMF_argmaxFinset` — the one-step bound of Proposition 8.
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-- A jump of the skeleton: which actor expresses which opinion.  This is the pair `(Aₙ, Oₙ)`
of the paper. -/
abbrev Jump (N M : ℕ) := Actor N × Opinion M

/-! ### The discrete measurable structure

Everything in sight is countable with measurable singletons, so every set is measurable and
every function is measurable.  These two lemmas name that fact for readability; they are both
`MeasurableSet.of_discrete` and `Measurable.of_discrete` in disguise. -/

section MeasurableStructure

/-- Every set of pressure matrices is measurable: the space is countable and discrete. -/
theorem measurableSet_pressure (s : Set (Pressure N M)) : MeasurableSet s :=
  MeasurableSet.of_discrete

/-- Every function out of the pressure matrices is measurable. -/
theorem measurable_of_pressure {γ : Type*} [MeasurableSpace γ] (f : Pressure N M → γ) :
    Measurable f := Measurable.of_discrete

/-- The expression operator of equation (1) is measurable in the matrix. -/
theorem measurable_express (a : Actor N) (o : Opinion M) :
    Measurable (express a o : Pressure N M → Pressure N M) := Measurable.of_discrete

end MeasurableStructure

/-! ### The jump rates of equation (3) -/

section Rates

/-- The jump rate `exp (β u (a, o))` of equation (3), written in the scaled coordinates of
`SocialNetwork.Defs`: since `u (a, o) = v (a, o) / (M - 1)`, the rate at the scaled matrix `v`
is `exp (β * v (a, o) / (M - 1))`.

There is no normalisation here: equation (3) is a generator, and these are genuine rates. -/
noncomputable def jumpRate (β : ℝ) (v : Pressure N M) (a : Actor N) (o : Opinion M) : ℝ :=
  Real.exp (β * (v a o : ℝ) / ((M : ℝ) - 1))

theorem jumpRate_pos (β : ℝ) (v : Pressure N M) (a : Actor N) (o : Opinion M) :
    0 < jumpRate β v a o := Real.exp_pos _

/-- The jump rate as an extended non-negative real, which is the shape `PMF.normalize` wants. -/
noncomputable def jumpWeight (β : ℝ) (v : Pressure N M) (p : Jump N M) : ℝ≥0∞ :=
  ENNReal.ofReal (jumpRate β v p.1 p.2)

theorem jumpWeight_pos (β : ℝ) (v : Pressure N M) (p : Jump N M) : 0 < jumpWeight β v p :=
  ENNReal.ofReal_pos.2 (jumpRate_pos β v p.1 p.2)

theorem jumpWeight_ne_top (β : ℝ) (v : Pressure N M) (p : Jump N M) : jumpWeight β v p ≠ ∞ :=
  ENNReal.ofReal_ne_top

variable [NeZero N] [NeZero M]

/-- The network is not empty: there is at least one actor and one opinion to express. -/
theorem univ_jump_nonempty (N M : ℕ) [NeZero N] [NeZero M] :
    (Finset.univ : Finset (Jump N M)).Nonempty :=
  ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩),
    Finset.mem_univ _⟩

theorem tsum_jumpWeight_ne_zero (β : ℝ) (v : Pressure N M) :
    (∑' p : Jump N M, jumpWeight β v p) ≠ 0 := by
  rw [Ne, ENNReal.tsum_eq_zero]
  intro h
  obtain ⟨p, -⟩ := univ_jump_nonempty N M
  exact (jumpWeight_pos β v p).ne' (h p)

omit [NeZero N] [NeZero M] in
theorem tsum_jumpWeight_ne_top (β : ℝ) (v : Pressure N M) :
    (∑' p : Jump N M, jumpWeight β v p) ≠ ∞ := by
  rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp]
  exact ENNReal.sum_ne_top.2 fun p _ => jumpWeight_ne_top β v p

/-- The law of the pair `(Aₙ, Oₙ)` given that the matrix at time `T_{n-1}` is `v`: the pair
`(a, o)` is chosen with probability proportional to its rate `exp (β u (a, o))` in equation (3). -/
noncomputable def jumpPMF (β : ℝ) (v : Pressure N M) : PMF (Jump N M) :=
  PMF.normalize (jumpWeight β v) (tsum_jumpWeight_ne_zero β v) (tsum_jumpWeight_ne_top β v)

theorem jumpPMF_apply (β : ℝ) (v : Pressure N M) (p : Jump N M) :
    jumpPMF β v p = jumpWeight β v p * (∑' q : Jump N M, jumpWeight β v q)⁻¹ := rfl

/-- Every pair has a positive chance of being chosen: the rates of equation (3) never vanish. -/
theorem jumpPMF_pos (β : ℝ) (v : Pressure N M) (p : Jump N M) : 0 < jumpPMF β v p := by
  rw [jumpPMF_apply]
  exact ENNReal.mul_pos (jumpWeight_pos β v p).ne'
    (ENNReal.inv_ne_zero.2 (tsum_jumpWeight_ne_top β v))

@[simp]
theorem support_jumpPMF (β : ℝ) (v : Pressure N M) : (jumpPMF β v).support = Set.univ :=
  Set.eq_univ_of_forall fun p => (PMF.apply_pos_iff _ p).1 (jumpPMF_pos β v p)

end Rates

/-! ### Definition 3: the skeleton kernel `Ũ^{β,u}` -/

section SkeletonKernel

variable [NeZero N] [NeZero M]

/-- **Definition 3.** The transition kernel of the skeleton process `Ũ^{β,u}`: from the matrix
`v`, choose the pair `(a, o)` with probability proportional to `exp (β u (a, o))` — the rate of
equation (3) — and move to `π^{a,o} (v)`.

The kernel is a plain function of `v` because the state space is countable and discrete, so
measurability is automatic (`ProbabilityTheory.Kernel.ofFunOfCountable`). -/
noncomputable def skeletonKernel (β : ℝ) : Kernel (Pressure N M) (Pressure N M) :=
  Kernel.ofFunOfCountable fun v => ((jumpPMF β v).map fun p => express p.1 p.2 v).toMeasure

theorem skeletonKernel_apply (β : ℝ) (v : Pressure N M) :
    skeletonKernel β v = ((jumpPMF β v).map fun p => express p.1 p.2 v).toMeasure := rfl

instance isMarkovKernel_skeletonKernel (β : ℝ) :
    IsMarkovKernel (skeletonKernel (N := N) (M := M) β) := by
  refine ⟨fun v => ?_⟩
  rw [skeletonKernel_apply]
  infer_instance

/-- The skeleton kernel is carried by the matrices that one expression reaches from `v`.  This
is what makes the chain a chain of *states of the model* rather than of arbitrary matrices. -/
theorem skeletonKernel_reachable (β : ℝ) (v : Pressure N M) :
    skeletonKernel β v {w | ∃ a o, w = express a o v} = 1 := by
  rw [skeletonKernel_apply]
  refine (PMF.toMeasure_apply_eq_one_iff _ MeasurableSet.of_discrete).2 ?_
  rw [PMF.support_map]
  rintro w ⟨p, -, rfl⟩
  exact ⟨p.1, p.2, rfl⟩

/-- The state space `S` of equation (2) is preserved by the skeleton with probability one.

This is `SocialNetwork.Trajectory.isState_state` read one step at a time: `S` is stable under
every `π^{a,o}` (`SocialNetwork.IsState.express`), and the kernel only moves along those. -/
theorem isState_skeletonKernel (β : ℝ) {v : Pressure N M} (hv : IsState v) :
    skeletonKernel β v {w | IsState w} = 1 := by
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = skeletonKernel β v {w | ∃ a o, w = express a o v} :=
        (skeletonKernel_reachable β v).symm
    _ ≤ skeletonKernel β v {w | IsState w} := by
        refine measure_mono ?_
        rintro w ⟨a, o, rfl⟩
        exact hv.express a o

theorem ae_isState_skeletonKernel (β : ℝ) {v : Pressure N M} (hv : IsState v) :
    ∀ᵐ w ∂(skeletonKernel β v), IsState w := by
  have h : skeletonKernel β v {w : Pressure N M | IsState w}ᶜ = 0 :=
    (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 (isState_skeletonKernel β hv)
  rw [MeasureTheory.ae_iff]
  exact h

end SkeletonKernel

/-! ### Trajectories as sample points

The sample space of the driving chain is `ℕ → Jump N M`, which *is* a `Trajectory N M`: the
two carry the same data.  `Trajectory.ofPath` is that identification, and it is what lets the
deterministic theorems of §5 be applied to a realisation without any almost-sure clause. -/

namespace Trajectory

/-- Read a path of expressed pairs as a trajectory.  With the index convention of
`SocialNetwork.Trajectory`, `ω 0` is the paper's `(A₁, O₁)`. -/
def ofPath (ω : ℕ → Jump N M) : Trajectory N M where
  actor n := (ω n).1
  opinion n := (ω n).2

@[simp]
theorem actor_ofPath (ω : ℕ → Jump N M) (n : ℕ) : (ofPath ω).actor n = (ω n).1 := rfl

@[simp]
theorem opinion_ofPath (ω : ℕ → Jump N M) (n : ℕ) : (ofPath ω).opinion n = (ω n).2 := rfl

/-- Read a finite history `(A₁, O₁), …, (A_{n+1}, O_{n+1})` as a trajectory, by repeating the
last pair forever.  Only the entries of index `≤ n` are ever used. -/
def ofHistory {n : ℕ} (h : (i : Finset.Iic n) → Jump N M) : Trajectory N M :=
  ofPath fun k => h ⟨min k n, Finset.mem_Iic.2 (min_le_right k n)⟩

theorem ofHistory_actor {n : ℕ} (h : (i : Finset.Iic n) → Jump N M) {j : ℕ} (hj : j ≤ n) :
    (ofHistory h).actor j = (h ⟨j, Finset.mem_Iic.2 hj⟩).1 := by
  have hmin : (⟨min j n, Finset.mem_Iic.2 (min_le_right j n)⟩ : Finset.Iic n)
      = ⟨j, Finset.mem_Iic.2 hj⟩ := Subtype.ext (min_eq_left hj)
  simp only [ofHistory, actor_ofPath, hmin]

theorem ofHistory_opinion {n : ℕ} (h : (i : Finset.Iic n) → Jump N M) {j : ℕ} (hj : j ≤ n) :
    (ofHistory h).opinion j = (h ⟨j, Finset.mem_Iic.2 hj⟩).2 := by
  have hmin : (⟨min j n, Finset.mem_Iic.2 (min_le_right j n)⟩ : Finset.Iic n)
      = ⟨j, Finset.mem_Iic.2 hj⟩ := Subtype.ext (min_eq_left hj)
  simp only [ofHistory, opinion_ofPath, hmin]

/-- The state after `n` expressions only depends on the first `n` expressed pairs. -/
theorem state_congr {T T' : Trajectory N M} (u : Pressure N M) :
    ∀ n : ℕ, (∀ k < n, T.actor k = T'.actor k) → (∀ k < n, T.opinion k = T'.opinion k) →
      T.state u n = T'.state u n := by
  intro n
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
      intro ha ho
      have hn : T.state u n = T'.state u n :=
        ih (fun k hk => ha k (by omega)) (fun k hk => ho k (by omega))
      rw [T.state_succ, T'.state_succ, hn, ha n (by omega), ho n (by omega)]

/-- Truncating a path to its first `n + 1` entries and reading the result as a history changes
no state up to time `n + 1`.  This is what makes the greedy event of the paper a cylinder. -/
theorem state_ofHistory_frestrictLe (u : Pressure N M) (ω : ℕ → Jump N M) {n k : ℕ}
    (hk : k ≤ n + 1) :
    (ofHistory (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)).state u k =
      (ofPath ω).state u k := by
  refine state_congr u k (fun j hj => ?_) (fun j hj => ?_)
  · rw [ofHistory_actor _ (show j ≤ n by omega), Preorder.frestrictLe_apply, actor_ofPath]
  · rw [ofHistory_opinion _ (show j ≤ n by omega), Preorder.frestrictLe_apply, opinion_ofPath]

end Trajectory

/-! ### The chain driven by the expressed pairs

`ProbabilityTheory.Kernel.traj` takes a family of kernels `κ n` that may depend on the whole
past, which is exactly what is needed here: the law of the `(n+2)`-nd pair depends on the
matrix at that time, which the first `n + 1` pairs determine. -/

section Driving

variable [NeZero N] [NeZero M]

/-- The kernel giving the law of the pair `(A_{n+2}, O_{n+2})` from the pairs
`(A₁, O₁), …, (A_{n+1}, O_{n+1})`: replay them from `u` and read off the rates of equation (3)
at the matrix so reached. -/
noncomputable def drivingKernel (β : ℝ) (u : Pressure N M) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Jump N M) (Jump N M) :=
  Kernel.ofFunOfCountable fun h => (jumpPMF β ((Trajectory.ofHistory h).state u (n + 1))).toMeasure

theorem drivingKernel_apply (β : ℝ) (u : Pressure N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Jump N M) :
    drivingKernel β u n h = (jumpPMF β ((Trajectory.ofHistory h).state u (n + 1))).toMeasure := rfl

instance isMarkovKernel_drivingKernel (β : ℝ) (u : Pressure N M) (n : ℕ) :
    IsMarkovKernel (drivingKernel β u n) := by
  refine ⟨fun h => ?_⟩
  rw [drivingKernel_apply]
  infer_instance

/-- The first expressed pair, read as a history of length one.  `Finset.Iic 0` is a
singleton, so this is a bijection; writing it out explicitly rather than through
`MeasurableEquiv.piUnique` keeps the computations below free of casts. -/
def toHistoryZero (z : Jump N M) : (i : Finset.Iic 0) → Jump N M := fun _ => z

omit [NeZero N] [NeZero M] in
@[simp]
theorem toHistoryZero_apply (z : Jump N M) (i : Finset.Iic 0) : toHistoryZero z i = z := rfl

omit [NeZero N] [NeZero M] in
theorem measurable_toHistoryZero : Measurable (toHistoryZero (N := N) (M := M)) :=
  Measurable.of_discrete

/-- **Definition 3**, as a law on realisations: the distribution of the sequence
`(Aₙ, Oₙ)ₙ` of expressed pairs of the skeleton `Ũ^{β,u}` started at `u`.

Its existence is the Ionescu-Tulcea theorem, `ProbabilityTheory.Kernel.traj`.  This is
`ProbabilityTheory.Kernel.trajMeasure` with the initial embedding written out. -/
noncomputable def pathMeasure (β : ℝ) (u : Pressure N M) : Measure (ℕ → Jump N M) :=
  Kernel.traj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) 0 ∘ₘ
    ((jumpPMF β u).toMeasure.map toHistoryZero)

theorem pathMeasure_def (β : ℝ) (u : Pressure N M) :
    pathMeasure β u =
      Kernel.traj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) 0 ∘ₘ
        ((jumpPMF β u).toMeasure.map toHistoryZero) := rfl

instance isProbabilityMeasure_pathMeasure (β : ℝ) (u : Pressure N M) :
    IsProbabilityMeasure (pathMeasure β u) := by
  rw [pathMeasure_def]
  have : IsProbabilityMeasure ((jumpPMF β u).toMeasure.map (toHistoryZero (N := N) (M := M))) :=
    Measure.isProbabilityMeasure_map measurable_toHistoryZero.aemeasurable
  infer_instance

/-- One step of the driving chain, pushed forward to the matrices, is one step of the skeleton
kernel.  This is the statement that the two constructions of this file are the same chain. -/
theorem map_drivingKernel (β : ℝ) (v : Pressure N M) :
    ((jumpPMF β v).map fun p => express p.1 p.2 v).toMeasure = skeletonKernel β v :=
  (skeletonKernel_apply β v).symm

end Driving

/-! ### The skeleton as a process, and the return time of Definition 3 -/

section Skeleton

/-- The skeleton `Ũ_n^{β,u} = U_{T_n}^{β,u}` of Definition 3, as a stochastic process on the
sample space of expressed pairs. -/
def skeleton (u : Pressure N M) (n : ℕ) (ω : ℕ → Jump N M) : Pressure N M :=
  (Trajectory.ofPath ω).state u n

@[simp]
theorem skeleton_zero (u : Pressure N M) (ω : ℕ → Jump N M) : skeleton u 0 ω = u := rfl

/-- `Ũ_n` depends only on the first `n` expressed pairs. -/
theorem skeleton_eq_comp (u : Pressure N M) (n : ℕ) :
    skeleton u n = (fun h : (i : Finset.Iic n) → Jump N M =>
        (Trajectory.ofHistory h).state u n) ∘
      Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n := by
  funext ω
  exact (Trajectory.state_ofHistory_frestrictLe u ω (Nat.le_succ n)).symm

theorem measurable_skeleton (u : Pressure N M) (n : ℕ) : Measurable (skeleton u n) := by
  rw [skeleton_eq_comp]
  exact Measurable.of_discrete.comp (Preorder.measurable_frestrictLe n)

/-- **Definition 3**, the return time `R̃^{β,u} (θ) = inf {n ≥ 1 : Ũ_n^{β,u} ∈ θ}`, valued in
`WithTop ℕ` so that `⊤` records that the skeleton never enters `θ`. -/
noncomputable def returnTime (u : Pressure N M) (θ : Set (Pressure N M)) :
    (ℕ → Jump N M) → WithTop ℕ :=
  MeasureTheory.hittingAfter (skeleton u) θ 1

theorem one_le_returnTime (u : Pressure N M) (θ : Set (Pressure N M)) (ω : ℕ → Jump N M) :
    ((1 : ℕ) : WithTop ℕ) ≤ returnTime u θ ω :=
  MeasureTheory.le_hittingAfter ω

end Skeleton

/-! ### The greedy event `ξₙ^u`

The paper's event

```
ξₙ^u := {(Aₙ, Oₙ) ∈ argmax_{(a,o)} U_{T_{n-1}}^{β,u} (a, o)}
```

is a condition on the realisation, which `SocialNetwork.IsGreedyAt` already expresses on a
`Trajectory`.  Here it becomes a subset of the sample space, and it is measurable because it
only constrains finitely many coordinates: it is a cylinder over a finite discrete space. -/

section GreedyEvent

/-- The paper's event `ξₙ^u`, as a subset of the sample space of the skeleton.

With the index convention of `SocialNetwork.Trajectory`, `greedyEvent u k` is `ξ_{k+1}^u`. -/
def greedyEvent (u : Pressure N M) (k : ℕ) : Set (ℕ → Jump N M) :=
  {ω | IsGreedyAt (Trajectory.ofPath ω) u k}

/-- The event `⋂_{j=1}^{n} ξⱼ^u` of Propositions 6, 7 and 8. -/
def greedyEvents (u : Pressure N M) (n : ℕ) : Set (ℕ → Jump N M) :=
  {ω | ∀ k < n, IsGreedyAt (Trajectory.ofPath ω) u k}

theorem greedyEvents_eq_iInter (u : Pressure N M) (n : ℕ) :
    greedyEvents u n = ⋂ k ∈ Set.Iio n, greedyEvent u k := by
  ext ω
  simp [greedyEvents, greedyEvent, Set.mem_Iio]

/-- The greedy event at step `k` only constrains the first `k + 1` expressed pairs, so reading
it off a truncated path gives the same answer. -/
theorem isGreedyAt_ofHistory_frestrictLe (u : Pressure N M) (ω : ℕ → Jump N M) {n k : ℕ}
    (hk : k ≤ n) :
    IsGreedyAt
        (Trajectory.ofHistory (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)) u k
      ↔ IsGreedyAt (Trajectory.ofPath ω) u k := by
  have hstate :=
    Trajectory.state_ofHistory_frestrictLe u ω (n := n) (k := k) (by omega)
  have hactor : (Trajectory.ofHistory
      (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)).actor k = (ω k).1 := by
    rw [Trajectory.ofHistory_actor _ hk, Preorder.frestrictLe_apply]
  have hopinion : (Trajectory.ofHistory
      (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)).opinion k = (ω k).2 := by
    rw [Trajectory.ofHistory_opinion _ hk, Preorder.frestrictLe_apply]
  simp only [IsGreedyAt, hstate, hactor, hopinion, Trajectory.actor_ofPath,
    Trajectory.opinion_ofPath]

theorem greedyEvent_eq_preimage (u : Pressure N M) (k : ℕ) :
    greedyEvent u k =
      Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) k ⁻¹'
        {h | IsGreedyAt (Trajectory.ofHistory h) u k} := by
  ext ω
  simp only [greedyEvent, Set.mem_setOf_eq, Set.mem_preimage]
  exact (isGreedyAt_ofHistory_frestrictLe u ω (le_refl k)).symm

theorem measurableSet_greedyEvent (u : Pressure N M) (k : ℕ) :
    MeasurableSet (greedyEvent u k) := by
  rw [greedyEvent_eq_preimage]
  exact Preorder.measurable_frestrictLe k MeasurableSet.of_discrete

theorem measurableSet_greedyEvents (u : Pressure N M) (n : ℕ) :
    MeasurableSet (greedyEvents u n) := by
  rw [greedyEvents_eq_iInter]
  exact MeasurableSet.biInter (Set.to_countable _) fun k _ => measurableSet_greedyEvent u k

end GreedyEvent

/-! ### Propositions 5, 6 and 7 on the sample space

Because the chain is driven by the expressed pairs, a sample point *is* a
`SocialNetwork.Trajectory` and the matrix at time `T_n` *is* `Trajectory.state`.  The
deterministic theorems of §5 therefore transfer verbatim and hold **pointwise** on the greedy
event — there is no almost-sure clause anywhere below, and none is needed. -/

section Transfer

variable {u : Pressure N M} {ω : ℕ → Jump N M}

/-- The state space `S` of equation (2) is preserved along every realisation. -/
theorem isState_state_ofPath (hu : IsState u) (ω : ℕ → Jump N M) (n : ℕ) :
    IsState ((Trajectory.ofPath ω).state u n) :=
  (Trajectory.ofPath ω).isState_state hu n

/-- **Proposition 5**, on every realisation: among the first `N` expressions at least one comes
from an actor carrying pressure below `N`. -/
theorem exists_rowSup_actor_lt_ofPath (hM : 2 ≤ M) (hu : IsState u) (ω : ℕ → Jump N M) :
    ∃ k < N, rowSup ((Trajectory.ofPath ω).state u k) ((Trajectory.ofPath ω).actor k)
      < N * (M - 1) :=
  exists_rowSup_actor_lt (Trajectory.ofPath ω) hM hu

/-- **Proposition 6**, on the event `⋂_{j=1}^{N} ξⱼ^u`: the whole matrix is confined to
`(-MN, N)` entrywise after `N` expressions. -/
theorem entry_mem_of_mem_greedyEvents (hM : 2 ≤ M) (hu : IsState u)
    (hω : ω ∈ greedyEvents u N) (a : Actor N) (p : Opinion M) :
    -((M : ℤ) * (N : ℤ) * ((M : ℤ) - 1)) < (Trajectory.ofPath ω).state u N a p ∧
      (Trajectory.ofPath ω).state u N a p < (N : ℤ) * ((M : ℤ) - 1) :=
  entry_mem_of_greedy (Trajectory.ofPath ω) hM hu (fun k hk => hω k hk) a p

/-- **The last step of Proposition 7**, on the event `⋂_{j=1}^{N} ξⱼ^v`: from a consensus state
for `o`, `N` greedy expressions land on a ladder supporting `o`. -/
theorem isLadder_state_of_mem_greedyEvents (hM : 2 ≤ M) (hN : 2 ≤ N) {o : Opinion M}
    {v : Pressure N M} (hv : IsConsensus o v) (hω : ω ∈ greedyEvents v N) :
    IsLadder o ((Trajectory.ofPath ω).state v N) :=
  isLadder_state (Trajectory.ofPath ω) hM hN hv (fun k hk => hω k hk)

/-- Every expression on the greedy event of a consensus state expresses the consensus
opinion. -/
theorem opinion_eq_of_mem_greedyEvents (hM : 2 ≤ M) (hN : 2 ≤ N) {o : Opinion M}
    {v : Pressure N M} (hv : IsConsensus o v) (hω : ω ∈ greedyEvents v N) {k : ℕ} (hk : k < N) :
    (ω k).2 = o :=
  opinion_eq_of_greedy (Trajectory.ofPath ω) hM hN hv (fun j hj => hω j hj) hk

end Transfer

/-! ### The arithmetic half of Proposition 8

The paper's proof of Proposition 8 rests on the observation that every entry of a state lies in
`ℤ + (1/(M-1)) ℤ = (1/(M-1)) ℤ`, so that an entry strictly below the maximum `y (v)` satisfies
`v (b, o) - y (v) ≤ -1/(M-1)`.  In the scaled coordinates used throughout, the entries are
integers by construction and this is the statement that two distinct integers differ by at
least `1`. -/

section GapEstimate

variable [NeZero N] [NeZero M]

/-- The paper's `y (v) = max {v (a, o) : a ∈ A, o ∈ O}`, the largest entry of the matrix. -/
noncomputable def entrySup (v : Pressure N M) : ℤ :=
  Finset.univ.sup' (univ_jump_nonempty N M) fun p : Jump N M => v p.1 p.2

theorem le_entrySup (v : Pressure N M) (a : Actor N) (o : Opinion M) : v a o ≤ entrySup v :=
  Finset.le_sup' (fun p : Jump N M => v p.1 p.2) (Finset.mem_univ (a, o))

/-- The paper's `Y (v) = {(a, o) : v (a, o) = y (v)}` is not empty. -/
theorem exists_entrySup (v : Pressure N M) : ∃ a o, v a o = entrySup v := by
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_mem_eq_sup' (univ_jump_nonempty N M) fun p : Jump N M => v p.1 p.2
  exact ⟨p.1, p.2, hp.symm⟩

/-- **The gap estimate behind Proposition 8.**  An entry strictly below the maximum is below it
by at least `1` in scaled coordinates, which is the paper's `v (b, o) - y (v) ≤ -1/(M-1)`.

The whole content of the paper's lattice argument is that the entries lie on a lattice; in
scaled coordinates that lattice is `ℤ`, and the estimate is `Int.lt_iff_add_one_le`. -/
theorem le_entrySup_sub_one {v : Pressure N M} {b : Actor N} {o : Opinion M}
    (h : v b o < entrySup v) : v b o ≤ entrySup v - 1 := by omega

/-- The greedy event at a matrix `v` is exactly the event that the expressed pair attains
`y (v)`. -/
theorem isGreedyAt_iff_entrySup (T : Trajectory N M) (u : Pressure N M) (k : ℕ) :
    IsGreedyAt T u k ↔ T.state u k (T.actor k) (T.opinion k) = entrySup (T.state u k) := by
  constructor
  · intro h
    refine le_antisymm (le_entrySup _ _ _) ?_
    obtain ⟨a, o, hao⟩ := exists_entrySup (T.state u k)
    exact hao ▸ h a o
  · intro h a o
    rw [h]
    exact le_entrySup _ _ _

end GapEstimate

/-! ### Remark 4: Bernoulli's inequality

Proposition 8 bounds the probability of `⋂_{j=1}^{m} ξⱼ^u` below by `(ζ_β)^m`, where

```
ζ_β = e^{β/(M-1)} / (e^{β/(M-1)} + M N).
```

Remark 4 turns that into the linear bound `(ζ_β)^m ≥ 1 - m M N e^{-β/(M-1)}`.  That step is a
statement about real numbers alone, and is proved here as such. -/

section Zeta

/-- The constant `ζ_β = e^{β/(M-1)} / (e^{β/(M-1)} + MN)` of Proposition 8. -/
noncomputable def zeta (N M : ℕ) (β : ℝ) : ℝ :=
  Real.exp (β / ((M : ℝ) - 1)) / (Real.exp (β / ((M : ℝ) - 1)) + (M : ℝ) * (N : ℝ))

theorem zeta_pos (N M : ℕ) (β : ℝ) : 0 < zeta N M β := by
  have h1 : (0 : ℝ) < Real.exp (β / ((M : ℝ) - 1)) := Real.exp_pos _
  have h2 : (0 : ℝ) ≤ (M : ℝ) * (N : ℝ) := by positivity
  unfold zeta
  exact div_pos h1 (by linarith)

theorem zeta_le_one (N M : ℕ) (β : ℝ) : zeta N M β ≤ 1 := by
  have h1 : (0 : ℝ) < Real.exp (β / ((M : ℝ) - 1)) := Real.exp_pos _
  have h2 : (0 : ℝ) ≤ (M : ℝ) * (N : ℝ) := by positivity
  unfold zeta
  rw [div_le_one (by linarith)]
  linarith

/-- The first half of Remark 4: `ζ_β ≥ 1 - MN e^{-β/(M-1)}`, which is `1/(1+x) ≥ 1 - x`. -/
theorem one_sub_le_zeta (N M : ℕ) (β : ℝ) :
    1 - (M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))) ≤ zeta N M β := by
  have hEpos : (0 : ℝ) < Real.exp (β / ((M : ℝ) - 1)) := Real.exp_pos _
  have hc : (0 : ℝ) ≤ (M : ℝ) * (N : ℝ) := by positivity
  unfold zeta
  rw [Real.exp_neg, le_div_iff₀ (by linarith)]
  have key : (1 - (M : ℝ) * (N : ℝ) * (Real.exp (β / ((M : ℝ) - 1)))⁻¹)
        * (Real.exp (β / ((M : ℝ) - 1)) + (M : ℝ) * (N : ℝ))
      = Real.exp (β / ((M : ℝ) - 1))
        - ((M : ℝ) * (N : ℝ)) * ((M : ℝ) * (N : ℝ)) * (Real.exp (β / ((M : ℝ) - 1)))⁻¹
        + ((M : ℝ) * (N : ℝ)) * (1 - (Real.exp (β / ((M : ℝ) - 1)))⁻¹
            * Real.exp (β / ((M : ℝ) - 1))) := by ring
  rw [key, inv_mul_cancel₀ hEpos.ne']
  have hnn : (0 : ℝ)
      ≤ ((M : ℝ) * (N : ℝ)) * ((M : ℝ) * (N : ℝ)) * (Real.exp (β / ((M : ℝ) - 1)))⁻¹ := by
    positivity
  linarith

/-- The elementary inequality behind Proposition 8: if the maximising pairs carry total weight
at least `A > 0` and the remaining pairs carry at most `M N A e^{-β/(M-1)}`, then the
maximising pairs carry at least the fraction `ζ_β` of the total weight. -/
theorem zeta_le_div_of_le (N M : ℕ) (β : ℝ) {A S T : ℝ} (hA : 0 < A) (hAS : A ≤ S)
    (hT0 : 0 ≤ T) (hT : T ≤ (M : ℝ) * (N : ℝ) * (A * Real.exp (-(β / ((M : ℝ) - 1))))) :
    zeta N M β ≤ S / (S + T) := by
  have hE : (0 : ℝ) < Real.exp (β / ((M : ℝ) - 1)) := Real.exp_pos _
  have hc : (0 : ℝ) ≤ (M : ℝ) * (N : ℝ) := by positivity
  have hS : (0 : ℝ) < S := lt_of_lt_of_le hA hAS
  have hST : (0 : ℝ) < S + T := by linarith
  rw [Real.exp_neg] at hT
  have hinv : Real.exp (β / ((M : ℝ) - 1)) * (Real.exp (β / ((M : ℝ) - 1)))⁻¹ = 1 :=
    mul_inv_cancel₀ hE.ne'
  have key : Real.exp (β / ((M : ℝ) - 1)) * T ≤ (M : ℝ) * (N : ℝ) * A := by
    calc Real.exp (β / ((M : ℝ) - 1)) * T
        ≤ Real.exp (β / ((M : ℝ) - 1))
            * ((M : ℝ) * (N : ℝ) * (A * (Real.exp (β / ((M : ℝ) - 1)))⁻¹)) :=
          mul_le_mul_of_nonneg_left hT hE.le
      _ = (M : ℝ) * (N : ℝ) * A
            * (Real.exp (β / ((M : ℝ) - 1)) * (Real.exp (β / ((M : ℝ) - 1)))⁻¹) := by ring
      _ = (M : ℝ) * (N : ℝ) * A := by rw [hinv, mul_one]
  have key2 : (M : ℝ) * (N : ℝ) * A ≤ (M : ℝ) * (N : ℝ) * S := by
    have h := mul_le_mul_of_nonneg_left hAS hc
    linarith
  unfold zeta
  rw [div_le_div_iff₀ (by linarith) hST]
  nlinarith [key, key2]

/-- **Remark 4.**  Proposition 8 together with Bernoulli's inequality gives, for every `m` and
every `β`,

```
(ζ_β)^m ≥ 1 - m M N e^{-β/(M-1)}.
```

This is the bound used in the proofs of Theorem 2 and Proposition 9.  It is stated here as the
real inequality that it is, so that it does not wait on the probabilistic content of
Proposition 8. -/
theorem one_sub_le_zeta_pow (N M : ℕ) (β : ℝ) (m : ℕ) :
    1 - (m : ℝ) * ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))))
      ≤ (zeta N M β) ^ m := by
  have hx0 : (0 : ℝ) ≤ (M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))) := by positivity
  have hz := one_sub_le_zeta N M β
  have hzpos := zeta_pos N M β
  rcases le_or_gt 1 ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))) with h | h
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hpow : (0 : ℝ) < (zeta N M β) ^ m := pow_pos hzpos m
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1)
        (by linarith :
          (0 : ℝ) ≤ (M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))) - 1)]
  · have h1 : (0 : ℝ) ≤ 1 - (M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))) := by linarith
    have h2 : (1 - (M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))) ^ m
        ≤ (zeta N M β) ^ m := pow_le_pow_left₀ h1 hz m
    have h3 := one_add_mul_le_pow
      (a := -((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))))) (by linarith) m
    rw [show (1 : ℝ) + (m : ℝ) * (-((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))))
          = 1 - (m : ℝ) * ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))) by ring,
        show (1 : ℝ) + -((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))))
          = 1 - (M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))) by ring] at h3
    exact h3.trans h2

end Zeta

/-! ### The one-step bound of Proposition 8

The paper's computation reads

```
P (ξ₁^v) = |Y(v)| e^{β y(v)} / (|Y(v)| e^{β y(v)} + ∑_{v(b,o) < y(v)} e^{β v(b,o)}) ≥ ζ_β,
```

and it uses exactly three facts: `|Y(v)| ≥ 1`, the gap estimate `v (b, o) ≤ y (v) - 1` for the
pairs that do not attain the maximum, and `|A × O| = M N` bounding their number. -/

section OneStep

variable [NeZero N] [NeZero M]

/-- The paper's `Y (v) = {(a, o) ∈ A × O : v (a, o) = y (v)}`, as a `Finset`. -/
noncomputable def argmaxFinset (v : Pressure N M) : Finset (Jump N M) :=
  Finset.univ.filter fun p => v p.1 p.2 = entrySup v

theorem mem_argmaxFinset {v : Pressure N M} {p : Jump N M} :
    p ∈ argmaxFinset v ↔ v p.1 p.2 = entrySup v := by
  simp [argmaxFinset]

/-- `|Y (v)| ≥ 1`: the maximum is attained. -/
theorem argmaxFinset_nonempty (v : Pressure N M) : (argmaxFinset v).Nonempty := by
  obtain ⟨a, o, hao⟩ := exists_entrySup v
  exact ⟨(a, o), mem_argmaxFinset.2 hao⟩

/-- The greedy event at step `k` says exactly that the pair expressed then lies in
`Y (Ũ_k^{β,u})`. -/
theorem mem_greedyEvent_iff (u : Pressure N M) (k : ℕ) (ω : ℕ → Jump N M) :
    ω ∈ greedyEvent u k ↔ ω k ∈ argmaxFinset (skeleton u k ω) := by
  rw [mem_argmaxFinset]
  exact isGreedyAt_iff_entrySup (Trajectory.ofPath ω) u k

/-- **The one-step bound of Proposition 8.**  Whatever the current matrix `v`, the pair chosen
at the next expression maximises the social pressure with probability at least `ζ_β`. -/
theorem zeta_le_jumpPMF_argmaxFinset (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    ENNReal.ofReal (zeta N M β) ≤ (jumpPMF β v).toMeasure (argmaxFinset v) := by
  have hMpos : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  -- the weight carried by a maximising pair
  have hmax : ∀ p ∈ argmaxFinset v,
      jumpRate β v p.1 p.2 = Real.exp (β * ((entrySup v : ℤ) : ℝ) / ((M : ℝ) - 1)) := by
    intro p hp
    unfold jumpRate
    rw [mem_argmaxFinset.1 hp]
  -- the weight carried by any other pair, using the gap estimate
  have hnonmax : ∀ p ∈ Finset.univ \ argmaxFinset v,
      jumpRate β v p.1 p.2
        ≤ Real.exp (β * ((entrySup v : ℤ) : ℝ) / ((M : ℝ) - 1))
          * Real.exp (-(β / ((M : ℝ) - 1))) := by
    intro p hp
    have hne : v p.1 p.2 ≠ entrySup v := fun hcon =>
      (Finset.mem_sdiff.1 hp).2 (mem_argmaxFinset.2 hcon)
    have hle : v p.1 p.2 ≤ entrySup v - 1 :=
      le_entrySup_sub_one (lt_of_le_of_ne (le_entrySup v p.1 p.2) hne)
    have hcast : ((v p.1 p.2 : ℤ) : ℝ) ≤ ((entrySup v : ℤ) : ℝ) - 1 := by exact_mod_cast hle
    unfold jumpRate
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : β * ((v p.1 p.2 : ℤ) : ℝ) ≤ β * (((entrySup v : ℤ) : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hcast hβ
    have h2 : β * ((v p.1 p.2 : ℤ) : ℝ) / ((M : ℝ) - 1)
        ≤ β * (((entrySup v : ℤ) : ℝ) - 1) / ((M : ℝ) - 1) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 (inv_pos.2 hMpos).le
    calc β * ((v p.1 p.2 : ℤ) : ℝ) / ((M : ℝ) - 1)
        ≤ β * (((entrySup v : ℤ) : ℝ) - 1) / ((M : ℝ) - 1) := h2
      _ = β * ((entrySup v : ℤ) : ℝ) / ((M : ℝ) - 1) + -(β / ((M : ℝ) - 1)) := by ring
  -- the two partial sums
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le
  have hT0 : (0 : ℝ) ≤ ∑ p ∈ Finset.univ \ argmaxFinset v, jumpRate β v p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le
  obtain ⟨p₀, hp₀⟩ := argmaxFinset_nonempty v
  have hAS : Real.exp (β * ((entrySup v : ℤ) : ℝ) / ((M : ℝ) - 1))
      ≤ ∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2 := by
    rw [← hmax p₀ hp₀]
    exact Finset.single_le_sum (fun p _ => (jumpRate_pos β v p.1 p.2).le) hp₀
  have hcard : (((Finset.univ \ argmaxFinset v).card : ℕ) : ℝ) ≤ (M : ℝ) * (N : ℝ) := by
    have h := Finset.card_le_card (Finset.subset_univ (Finset.univ \ argmaxFinset v))
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.mul_comm] at h
    exact_mod_cast h
  have hT : (∑ p ∈ Finset.univ \ argmaxFinset v, jumpRate β v p.1 p.2)
      ≤ (M : ℝ) * (N : ℝ)
        * (Real.exp (β * ((entrySup v : ℤ) : ℝ) / ((M : ℝ) - 1))
          * Real.exp (-(β / ((M : ℝ) - 1)))) := by
    have h1 := Finset.sum_le_card_nsmul (Finset.univ \ argmaxFinset v)
      (fun p => jumpRate β v p.1 p.2)
      (Real.exp (β * ((entrySup v : ℤ) : ℝ) / ((M : ℝ) - 1))
        * Real.exp (-(β / ((M : ℝ) - 1)))) hnonmax
    rw [nsmul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  -- the real inequality
  have hreal : zeta N M β
      ≤ (∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2)
        / ((∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2)
          + ∑ p ∈ Finset.univ \ argmaxFinset v, jumpRate β v p.1 p.2) :=
    zeta_le_div_of_le N M β (Real.exp_pos _) hAS hT0 hT
  -- transport it to the measure
  have hw : ∀ s : Finset (Jump N M),
      (∑ p ∈ s, jumpWeight β v p) = ENNReal.ofReal (∑ p ∈ s, jumpRate β v p.1 p.2) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le]
    rfl
  have hsplit : (∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2)
      + (∑ p ∈ Finset.univ \ argmaxFinset v, jumpRate β v p.1 p.2)
      = ∑ p : Jump N M, jumpRate β v p.1 p.2 := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ _)
  have hST : (0 : ℝ) < (∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2)
      + ∑ p ∈ Finset.univ \ argmaxFinset v, jumpRate β v p.1 p.2 := by
    have hpos := Real.exp_pos (β * ((entrySup v : ℤ) : ℝ) / ((M : ℝ) - 1))
    linarith
  have htsum : (∑' q : Jump N M, jumpWeight β v q)
      = ENNReal.ofReal ((∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2)
        + ∑ p ∈ Finset.univ \ argmaxFinset v, jumpRate β v p.1 p.2) := by
    rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp,
      hw Finset.univ, hsplit]
  rw [PMF.toMeasure_apply_finset]
  simp only [jumpPMF_apply]
  rw [← Finset.sum_mul, hw (argmaxFinset v), htsum, ← ENNReal.ofReal_inv_of_pos hST,
    ← ENNReal.ofReal_mul hS0, ← div_eq_mul_inv]
  exact ENNReal.ofReal_le_ofReal hreal

end OneStep

end SocialNetwork
