# What Mathlib provides, and what it does not

This file is the engineering companion to the blueprint.  The **blueprint itself** —
the correspondence between the numbered statements of arXiv:2607.19651 and their Lean
counterparts, the dependency graph, and the corrections that formalising the paper
surfaced — lives in [`blueprint/src/content.tex`](src/content.tex) and renders as a web
page and a pdf.  That is the contract between the paper and the repository; a change to
the code updates it in the same commit.

Three files at the root divide the rest between them.
[`STATUS.md`](../STATUS.md) is the generated index of every statement and its status;
[`FOR-THE-AUTHORS.md`](../FOR-THE-AUTHORS.md) collects what formalising has not been able
to close and what each item asks of the authors — the written proofs that do not compose,
the statements that had to be changed, and the two axioms; and
[`CONVENTIONS.md`](../CONVENTIONS.md) is how the translation is written.  What is blocked
*there* is blocked on the paper; what is blocked here is blocked on Mathlib.

What is in this file is the audit that has no place in a mathematical blueprint: exact
declaration names, file paths and line numbers for what Mathlib does and does not provide.
It was checked against the sources of the pinned revision (`lake-manifest.json`,
Mathlib `v4.33.0` = `db584cd6`).  **Do not trust it against a different revision without
re-checking**; the fastest way to re-check is to clone Mathlib at the pinned tag and grep,
which is how it was written in the first place.

## Resolved: constructing the process, in discrete *and* continuous time

An early draft listed "construction of the process from a generator" as the principal gap.
It is not one.

**Discrete time.**  `ProbabilityTheory.Kernel.traj`
(`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:518`) is the Ionescu-Tulcea theorem, and
it assumes nothing about the state spaces beyond `[MeasurableSpace]` — no standard Borel, no
Polish, no separability.  It also allows the kernels to depend on the *whole past*, which is
what `SocialNetwork.Skeleton` exploits to drive the chain by the expressed pairs rather than
by the matrices.

**Continuous time.**  Nor is the jump process a gap, once one notices that its jump-hold
representation is a discrete-time chain carrying one extra real coordinate.  Taking the state
of that chain to be

```
(Aₙ, Oₙ, holding time)   ∈   Actor N × Opinion M × ℝ
```

and the holding time to be `ProbabilityTheory.expMeasure (q_β v)`
(`Mathlib/Probability/Distributions/Exponential.lean:96`) turns `Kernel.traj` into a
construction of the whole process.  `SocialNetwork.ContinuousTime` does exactly that, and
from it the jump times `Tₙ`, the process `U_t`, the transition semigroup `P_t` and the hitting
times `R^{β,u}(θ)` are all plain definitions.

Two remarks on why this is cheap here.  The state space `Pressure N M` is countable with
measurable singletons, hence `DiscreteMeasurableSpace`, so every subset is measurable and
every function out of it is measurable; and the law of the next step depends on the history
only through the current matrix, so the one measurability obligation that survives the move to
the uncountable sample space is discharged by factoring through that countable space.

## Resolved: the strong law, and the infinite product measure

Proposition 18 rewrites a sum over opinion words as an expectation over an i.i.d. uniform
sequence and keeps only the words whose empirical frequencies have settled.  Both halves of
that are in Mathlib at the pinned revision, and neither needed anything added.

* `MeasureTheory.Measure.infinitePi` (`Mathlib/Probability/ProductMeasure.lean:358`) is the
  product of an arbitrary family of probability measures, built through `Kernel.traj` and
  Carathéodory.  `infinitePi_pi` (line 405) gives the mass of a finite box — which is all
  the cylinder computation needs — and `infinitePi_map_eval` (line 481) the law of one
  coordinate.
* `ProbabilityTheory.iIndepFun_infinitePi`
  (`Mathlib/Probability/Independence/InfinitePi.lean:127`) says the coordinates of that
  measure are independent, in the `iIndepFun` form the strong law wants.
* `ProbabilityTheory.strong_law_ae_real` (`Mathlib/Probability/StrongLaw.lean:598`) is
  Etemadi's strong law: pairwise independence and identical distribution suffice, which is
  more than enough for indicators of a letter.

`SocialNetwork/Frequencies.lean` assembles the three into `uniformSeq`, the law of an i.i.d.
uniform word, and proves that the paper's event `E_ε^k` has positive probability for some
`k`.  The one thing that had to be written by hand is the bridge back to counting: at every
horizon `n`, the words of length `n` meeting the constraint up to `n` carry at least the
mass `P(E_ε^k)` of the uniform law on the `M^n` words.  That is `uniformSeq_freqGood_le`,
and it is subadditivity plus `infinitePi_pi` on singleton boxes.

## Resolved without Mathlib: the Markov property

**Mathlib has no strong Markov property.**  At the pinned revision there is not one
occurrence of "strong Markov" in the library.  The only statement of a Markov property is the
*weak* one for Brownian motion, `ProbabilityTheory.IsPreBrownianReal.indepFun_shift`
(`Mathlib/Probability/BrownianMotion/Basic.lean:232`), which is about independence of Gaussian
increments and does not transport.

Theorem 4 part 1 needs one, and mostly does not.  The paper writes "the strong Markov property
at time `T_N`", but the whole argument is about the sequence `(A_n)` of expressing actors —
that is, about the skeleton — and for the skeleton `T_N` is the **deterministic** index `N`.
What is used there is the simple Markov property at a deterministic time.  The genuine
stopping times are the failure times, and for a discrete-time chain the strong Markov property
at those follows from the simple one by decomposing over their countably many values; in
`SocialNetwork/BiasedResults.lean` that decomposition is done directly on the failure
*events*, so no stopping-time API is needed.  (Mathlib has one if it ever is:
`MeasureTheory.IsStoppingTime` and `IsStoppingTime.measurableSpace`,
`Mathlib/Probability/Process/Stopping.lean:75` and `:444`.)

Mathlib's `Kernel.traj` scaffolding does carry the deterministic-time statement, in the very
formalism this project uses:

* `ProbabilityTheory.Kernel.traj_comp_partialTraj`
  (`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:575`) — `traj κ b ∘ₖ partialTraj κ a b =
  traj κ a`, the decomposition at a deterministic time.
* `Kernel.partialTraj_compProd_traj` (line 656) — the joint law of the past and the
  trajectory.
* `Kernel.condExp_traj` (line 720) — `E[f | F_b] = ∫ f d(traj κ b …)`, which is the shape of
  the paper's display `E[1_{U_{T_N} ∈ B_N} P_{U_{T_N}}(…)]`.

None of these was used in the end.  They decompose the *same* family of kernels, whereas the
argument needs the shifted trajectory to have the law of the chain **started afresh at the
profile reached** — a statement about this particular kernel family, since
`biasedDrivingKernel γ β u n h` depends on the past only through `stateAfterHistory u h (n+1)`.
That is `SocialNetwork.Bias.pathMeasure_restart`, and it is proved from the exact law of a
cylinder (`pathMeasure_cylinder`) by uniqueness of measures on the π-system of cylinders.  The
exact law is the same induction that gives the one-step bound of Propositions 17 and 24, with
the one-step kernel evaluated at a singleton instead of bounded below.

## Resolved without Mathlib: Kac's lemma, and the skeleton's Markov property

**Mathlib has no Kac lemma.**  Every `Kac` in the library is a Kac–Moody algebra.  Proposition
9 was recorded here as waiting on one; it was not, and the entry was wrong in the same way the
`measurable_hittingTimeCts` entry below was wrong.

The paper opens the proof of Proposition 9 with the *identity*
`1/μ̃(u) = E[R̃^u(u)]`, and the identity does need irreducibility: with two absorbing states and
`μ̃ = (½, ½)`, the return time to either is `1`, not `2`.  But the proof needs only
`μ̃(u) · E[R̃^u(u)] ≤ 1`, and **that inequality holds for every invariant probability measure**,
with no irreducibility, no recurrence and no existence theorem.  So it does not wait on
Doeblin either.

`SocialNetwork/Kac.lean` proves it, for a Markov kernel on a countable measurable space, in
about a hundred lines:

* `SocialNetwork.kac_identity` — the finite-horizon identity: the event of visiting `u` before
  time `m`, decomposed over the *last* such visit.  Invariance enters once, as
  `∫ (κ g) dμ = ∫ g dμ`; the rest splits an integral at the singleton `{u}`.
* `SocialNetwork.kac_tsum_le` — `μ {u} · ∑_n P_u(R_u > n) ≤ 1`.
* `SocialNetwork.measure_singleton_le_of_avoid` — the form Proposition 9 consumes.

From Mathlib it uses `ProbabilityTheory.Kernel.Invariant`
(`Mathlib/Probability/Kernel/Invariance.lean:39`), `MeasureTheory.Measure.lintegral_bind`
(`Mathlib/MeasureTheory/Measure/GiryMonad.lean:285`), `Measure.restrict_singleton` and
`lintegral_add_compl` (`Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:630`), and
`ENNReal.tsum_le_of_sum_range_le`.  Nothing else.  Poincaré recurrence
(`Mathlib/Dynamics/Ergodic/Conservative.lean`) is not used: it is about a measure-preserving
*map*, and the shift on this repository's sample space is not one, since a path is a sequence
of *jumps* read against a starting matrix.

Applying it needs the skeleton's avoidance probabilities, which are defined by a recursion on
the kernel, to be identified with probabilities of events on realisations.  That is one
application of the Markov property at time `1`, and `SocialNetwork/Markov.lean` carries it:
`SocialNetwork.pathMeasure_cylinder` (the exact law of a cylinder),
`SocialNetwork.pathMeasure_restart` (the Markov property at a deterministic time) and
`SocialNetwork.kacAvoid_skeletonKernel` (the bridge).  The first two are the transposition to
the skeleton of the biased lemmas of the section above, proved the same way.

## Still missing, in DISCRETE time

These block Theorem 1.2 and everything downstream of it.  Items 1–3 are one gap seen from
three sides.

1. **Doeblin's condition ⇒ a unique invariant measure.**  Nothing.  `grep` over the whole tree
   returns zero hits for `Doeblin`, `minorisation`, `minorization`.
2. **The theory around `Kernel.Invariant`.**  The definition exists
   (`Mathlib/Probability/Kernel/Invariance.lean`) — `μ.bind κ = μ` — together with
   `Invariant.comp`, `IsReversible` and `IsReversible.invariant`.  That is the entire file, and
   **no other file in Mathlib uses `Kernel.Invariant`**: there is no existence result, no
   uniqueness result, no convergence result, not even on a finite state space.
3. **Irreducibility.**  `ProbabilityTheory.Kernel.IsIrreducible`
   (`Mathlib/Probability/Kernel/Irreducible.lean`) is the Meyn–Tweedie definition, two trivial
   instances and one monotonicity lemma.  Nothing is derived from it.
4. **Recurrence for chains, and return times.**  Nothing (`returnTime`, "return time": zero
   hits).  `Mathlib/Dynamics/Ergodic/Conservative.lean` has Poincaré recurrence, but for a
   measure-preserving *map*, which does not transport to a kernel.  Nothing in this repository
   waits on this any more: it was here for Kac's lemma, and Kac's inequality turned out to need
   neither recurrence nor a return time as an object — only the avoidance probabilities, which
   are a recursion on the kernel.
5. **Total-variation distance between measures.**  Nothing usable: `totalVariation` exists only
   for signed and vector measures (Jordan decomposition), not as the distance that uniform
   ergodicity is stated in.

## Still missing, in CONTINUOUS time

6. **Non-explosion criteria.**  Theorem 1.1 is proved by sandwiching the jump times between two
   Poisson processes.  **Mathlib has no Poisson point process**; what it has is the Poisson
   *distribution* on `ℕ` (`ProbabilityTheory.poissonMeasure`,
   `Mathlib/Probability/Distributions/Poisson/Basic.lean`) and the Poisson limit theorem.  An
   earlier draft of this blueprint asserted the opposite; that was wrong.
7. **The transfer `μ ∝ μ̃ / q`** of equation (13), the bijection between the stationary laws of
   the jump chain and of the process.  Nothing, and it needs 1–5 above to be worth stating.
8. **Quantitative convergence to `Exp(1)`.**  `TendstoInDistribution`
   (`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`) is new and makes the
   qualitative half of Theorem 3 expressible, with the continuous mapping theorem and
   Slutsky's theorem available; `Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean`
   metrises weak convergence.  What is absent is the Kolmogorov-type *bound*, and the
   criterion of [LM22] that Proposition 12 invokes.

## Which theorems depend on which

Theorems 2 and 3 are, in the paper's own architecture, statements about the **skeleton**: the
continuous-time versions follow from the discrete ones through the transfer (13) and the
control of the holding times.  So they are blocked by items 1–3, not by 6.  Only Theorem 1.1 —
and its biased twin Theorem 16 — genuinely needs the continuous-time item 6.

The shortest path to Theorem 2 is therefore item 1 alone.  Proposition 9 no longer waits on
Mathlib at all: it is proved from Proposition 7, Remark 5, the bound of Proposition 8
(`SocialNetwork.zeta_pow_le_pathMeasure_greedyEvents`) and Kac's inequality, modulo the one
step its own proof asserts (`SocialNetwork.skeleton_ne_of_greedy`).  Theorem 2.1 follows from
it by (13) once `μ̃` exists, which is item 1.

## A smaller gap, outside probability — closed, but still a gap

`N` distinct naturals sum to at least `0 + 1 + ⋯ + (N-1)`.  Mathlib has no lemma to this
effect, and none from which it follows in one step.  The route it suggests is
`Finset.orderEmbOfFin` (`Mathlib/Data/Finset/Sort.lean:194`) to enumerate the image in
increasing order, plus "a strictly monotone `Fin N → ℕ` dominates the identity" — but
`StrictMono.le_apply` (`Mathlib/Order/WellFounded.lean:248`) is stated only for
endomorphisms `f : β → β`, so the `Fin N → ℕ` case would have to be redone by hand.

`SocialNetwork.Bias.sum_range_card_le_sum` proves it a different way, and avoids that step
entirely: induct on the largest element with `Finset.induction_on_max`
(`Mathlib/Data/Finset/Max.lean:460`).  Adjoining a new maximum `a` to `s` adds `a` to the sum
and `#s` to the bound, and `a ≥ #s` because `s ⊆ range a`.
`SocialNetwork.Bias.sum_ge_of_injective` is the image of `f` read through it.

The Mathlib gap itself is unchanged: this belongs upstream, in `Mathlib/Data/Finset/Card.lean`
or beside `Finset.sum_range_id_mul_two`, not in a paper formalisation.

## `measurable_hittingTimeCts`: filed as routine, refiled as blocked, and neither

This entry is kept as a record of two wrong calls in a row, because both were made
here and both were about what Mathlib supplies.

An early draft listed `SocialNetwork.measurable_hittingTimeCts` alongside
`SocialNetwork.measurable_process`, on the grounds that both only see `jumpCount`.  That
was wrong: `process` is evaluated at one `t`, the hitting time is an infimum over the
uncountable family `{t ≥ 0}`.

The correction was wrong too.  It said the reduction to a countable infimum needs the path
`t ↦ U_t (ω)` to be right-continuous; that right-continuity fails on realisations with a
negative holding time, or whose jump times accumulate from the right; and that the statement
therefore wanted an almost-sure formulation or an argument through the null set.  Every
clause of that is true except the first, and the first is the one that mattered.
Right-continuity is *a* route to the reduction, not the only one.

Both lemmas are now proved, statements unchanged, for every `ω`.  What the proof uses is the
shape of the level sets of `jumpCount ω ·`: below the explosion time the infimum of a level
set is attained, at `max (Tₖ, 0)`, and on the explosion event the junk value of `sSup`
persists to the right, so the rationals above a time serve in its place.  The countable
family `{max (Tₖ, 0)} ∪ (ℚ ∩ [0, ∞))` meets the infimum outright.  See
`SocialNetwork.sInf_image_eq_hittingCandidates`, which is stated for an arbitrary map from
jump counts to states and is therefore shared by both models.

**Nothing was missing from Mathlib here.**  The lesson for the rest of this file: an
obstruction recorded as "the library does not provide it" is a claim about a route, and a
route is easier to be wrong about than a name that is absent.  The entries below are of the
second kind — a `grep` that returns nothing, or a file whose whole contents are enumerated —
which is why they are cheap to falsify and this one was not.

## How to re-check this file

```sh
git clone --depth 1 --branch v4.33.0 https://github.com/leanprover-community/mathlib4
grep -rn 'Doeblin\|minorisation\|returnTime' mathlib4/Mathlib --include='*.lean'
grep -rln 'Kernel.Invariant' mathlib4/Mathlib --include='*.lean'
```

The claims above are all of this shape: a name that is absent, or a file whose entire
contents are enumerated.  Each is cheap to falsify, which is the point.
