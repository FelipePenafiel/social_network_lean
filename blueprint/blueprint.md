# What Mathlib provides, and what it does not

This file is the engineering companion to the blueprint.  The **blueprint itself** —
the correspondence between the numbered statements of arXiv:2607.19651 and their Lean
counterparts, the dependency graph, and the three corrections that formalising the paper
surfaced — lives in [`blueprint/src/content.tex`](src/content.tex) and renders as a web
page and a pdf.  That is the contract between the paper and the repository; a change to
the code updates it in the same commit.

A third file, [`FOR-THE-AUTHORS.md`](../FOR-THE-AUTHORS.md) at the root, collects what
formalising has not been able to close and what each item asks of the authors: the written
proofs that do not compose, the statements that had to be changed, and the one axiom.  What
is blocked *there* is blocked on the paper; what is blocked here is blocked on Mathlib.

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

## Still missing, in DISCRETE time

These block Theorem 1.2, Proposition 9, Corollary 10 and everything downstream.

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
4. **Kac's lemma**, `1/μ̃(u) = E[R̃^u(u)]`, used by Proposition 9.  Nothing: every `Kac` in
   Mathlib is a Kac–Moody algebra.
5. **Recurrence for chains, and return times.**  Nothing (`returnTime`, "return time": zero
   hits).  `Mathlib/Dynamics/Ergodic/Conservative.lean` has Poincaré recurrence, but for a
   measure-preserving *map*, which does not transport to a kernel.
6. **Total-variation distance between measures.**  Nothing usable: `totalVariation` exists only
   for signed and vector measures (Jordan decomposition), not as the distance that uniform
   ergodicity is stated in.

## Still missing, in CONTINUOUS time

7. **Non-explosion criteria.**  Theorem 1.1 is proved by sandwiching the jump times between two
   Poisson processes.  **Mathlib has no Poisson point process**; what it has is the Poisson
   *distribution* on `ℕ` (`ProbabilityTheory.poissonMeasure`,
   `Mathlib/Probability/Distributions/Poisson/Basic.lean`) and the Poisson limit theorem.  An
   earlier draft of this blueprint asserted the opposite; that was wrong.
8. **The transfer `μ ∝ μ̃ / q`** of equation (13), the bijection between the stationary laws of
   the jump chain and of the process.  Nothing, and it needs 1–5 above to be worth stating.
9. **Quantitative convergence to `Exp(1)`.**  `TendstoInDistribution`
   (`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`) is new and makes the
   qualitative half of Theorem 3 expressible, with the continuous mapping theorem and
   Slutsky's theorem available; `Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean`
   metrises weak convergence.  What is absent is the Kolmogorov-type *bound*, and the
   criterion of [LM22] that Proposition 12 invokes.

## Which theorems depend on which

Theorems 2 and 3 are, in the paper's own architecture, statements about the **skeleton**: the
continuous-time versions follow from the discrete ones through the transfer (13) and the
control of the holding times.  So they are blocked by items 1–5, not by 7.  Only Theorem 1.1 —
and its biased twin Theorem 16 — genuinely needs the continuous-time item 7.

The shortest path to Theorem 2 is therefore: Doeblin ⇒ unique invariant measure for a
countable-state kernel (item 1), then Kac (item 4), then Proposition 9 follows from
Proposition 7, Remark 5 and the bound of Proposition 8 that is already proved
(`SocialNetwork.zeta_pow_le_pathMeasure_greedyEvents`), and Theorem 2.1 follows from
Proposition 9 by (13).

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

## `measurable_hittingTimeCts` is not the routine lemma it was filed as

An earlier draft listed `SocialNetwork.measurable_hittingTimeCts` alongside
`SocialNetwork.measurable_process`, on the grounds that both only see `jumpCount`.  They do
not sit at the same depth, and `measurable_process` being done now makes the difference plain.

`process` is evaluated at one `t`.  The hitting time is an infimum over the **uncountable**
family `{t : 0 ≤ t}`, so it needs the path `t ↦ U_t (ω)` to be right-continuous — that is what
reduces the infimum to a countable one.  Right-continuity holds where the jump times increase,
and `holdingTime` is a plain real coordinate of the sample space: `expMeasure`
(`Mathlib/Probability/Distributions/Exponential.lean:96`) charges only `[0, ∞)`, so it is
positive *almost surely*, not for every `ω`.  On a realisation with a negative holding time,
or whose jump times accumulate from the right at some `t`, `jumpCount ω ·` is not
right-continuous and the reduction fails pointwise.

So the statement wants an almost-sure formulation, or a proof that goes through the null set.
Neither is a cylinder argument.

## How to re-check this file

```sh
git clone --depth 1 --branch v4.33.0 https://github.com/leanprover-community/mathlib4
grep -rn 'Doeblin\|minorisation\|returnTime' mathlib4/Mathlib --include='*.lean'
grep -rln 'Kernel.Invariant' mathlib4/Mathlib --include='*.lean'
```

The claims above are all of this shape: a name that is absent, or a file whose entire
contents are enumerated.  Each is cheap to falsify, which is the point.
