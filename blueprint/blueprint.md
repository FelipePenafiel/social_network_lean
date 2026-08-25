# Blueprint — arXiv:2607.19651

*Metastability and phase transition in a social network model with multiple opinions*,
Felipe Penafiel, Kádmo Laxa.

> **Where to look.** The statement-by-statement correspondence now also lives in
> `blueprint/src/content.tex`, a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
> document that renders as a web page with a dependency graph. The two overlap in
> their tables. What is *only* here is the audit of Mathlib below — exact names,
> files and line numbers for what the library does and does not provide — which
> belongs to the engineering of this repository rather than to the mathematics of
> the paper. Keep both in step, or tell the maintainer to fold the tables into the
> LaTeX blueprint and leave this file the audit alone.

This file is the working map between the numbered statements of the paper and their Lean
counterparts. Every statement of the paper appears here, whether or not it has been
formalised, so that the gap between the article and the repository is always explicit.

Status legend:

| Symbol | Meaning |
| --- | --- |
| ✅ | Stated **and** proved in Lean, no `sorry` |
| 🟡 | Stated in Lean, proof is a `sorry` |
| ⬜ | Not stated in Lean |

Every numbered statement of the paper is now *stated* in Lean; the remaining question about
each is whether its proof is formalised. A 🟡 entry is a faithful Lean statement whose proof
this development does not supply — either because the argument rests on Mathlib
infrastructure that does not exist (Doeblin, Kac, Poisson point processes: see
§"Infrastructure gaps"), or because the written proof does not compose as it stands (Lemmas
19 and 20: see §"Two points in Appendix A"). The `sorry`s are inventoried by CI on every run;
what CI *rejects* is a `sorry` reaching a declaration listed as complete in
`.github/workflows/ci.yml`.

## Conventions

The paper's pressure matrices have entries in `ℤ + (1/(M-1))ℤ = (1/(M-1))ℤ`. The
formalisation works throughout in **scaled coordinates**

```
v (a, o) := (M - 1) * u (a, o) ∈ ℤ
```

so that `π^{a,o}` becomes an operator on integer matrices (`+ (M-1)` on the expressed
column, `- 1` elsewhere). This is a bijective positive rescaling, so it changes no
statement, and it turns the lattice estimate underlying Proposition 8 — that distinct
entries differ by at least `1/(M-1)` — into the statement that distinct integers differ by
at least `1`.

Standing assumptions of the paper: `N ≥ 3` actors, `M ≥ 2` opinions. These are carried as
explicit hypotheses on the statements that need them rather than as global variables, so
that each result records exactly what it uses. In practice `hM : 2 ≤ M` is what the proofs
so far require; `N ≥ 3` has not been needed, since `N ≥ 1` already follows from `IsState`
(it supplies an actor) and nothing yet uses more.

## Section 2 — Model and main results

| Paper | Statement | Lean | Status |
| --- | --- | --- | --- |
| eq. (1) | operator `π^{a,o}` | `SocialNetwork.express` | ✅ |
| eq. (2) | state space `S` | `SocialNetwork.IsState` | ✅ |
| after (2) | `S` is stable under every `π^{a,o}` | `SocialNetwork.IsState.express` | ✅ |
| — | trust is conserved by listening, reset by expressing | `SocialNetwork.trust_express` | ✅ |
| eq. (3) | jump rates `exp (β u (a,o))` | `SocialNetwork.jumpRate` | ✅ |
| eq. (3) | ↳ the induced jump law on `A × O` | `SocialNetwork.jumpPMF` | ✅ |
| eq. (3) | generator `G` of the **continuous-time** jump process | `SocialNetwork.generator` | ✅ |
| Thm 1.1 | non-explosion, `P(sup Tₘ = ∞) = 1` | `SocialNetwork.nonExplosion` | 🟡 |
| Thm 1.2 | existence and uniqueness of `μ^β` | `SocialNetwork.existsUnique_invariantCts` | 🟡 |
| Def 1 | ladder sets `L^o`, `L` | `SocialNetwork.IsLadder` | ✅ |
| Thm 2.1 | `μ^β (L) ≥ 1 - C e^{-β/(M-1)}` | `SocialNetwork.measure_ladderSet_ge` | 🟡 |
| Thm 2.2 | hitting time of `L` vanishes as `β → ∞` | `SocialNetwork.tendsto_hittingTime_ladderSet` | 🟡 |
| Def 2 | consensus sets `C^o`, `C^{-o}` | `SocialNetwork.IsConsensus` | ✅ |
| — | `L^o ⊆ C^o` | `SocialNetwork.IsLadder.isConsensus` | ✅ |
| Thm 3 | metastability: `R^{β,u}(C^{-o})/E[·] → Exp(1)` | `SocialNetwork.metastability` | 🟡 |

## Section 3 — Communication bias and phase transition

| Paper | Statement | Lean | Status |
| --- | --- | --- | --- |
| eq. (6) | memory profile `(nₐ, cₚ)` | `SocialNetwork.Bias.Memory` | ✅ |
| eq. (6) | the row `u (a, p) = cₚ (1+γ) - γ nₐ` | `SocialNetwork.Bias.Memory.pressure` | ✅ |
| eq. (5) | operator `π_α^{a,o}` | `SocialNetwork.Bias.Memory.hear` | ✅ |
| Rmk 1 | `S^α` stable under `π_α^{a,o}` | `SocialNetwork.Bias.Memory.pressure_hear` | ✅ |
| Rmk 1 | `∑_p u (a, p) = nₐ (M-1) α` | `SocialNetwork.Bias.Memory.sum_pressure_eq` | ✅ |
| Rmk 1 | `u (a, p) ∈ ℤ + γℤ` | `…Profile.pressure_mem_addSubgroup` | ✅ |
| Rmk 1 | a row is null if `nₐ = 0` | `…Memory.pressure_eq_zero_of_heard_eq_zero` | ✅ |
| Rmk 1 | … and only if, when `(M-1) α ≠ 0`; hence `0 ∉ S^α` | `…IsBiasedState.pressure_ne_zero` | ✅ |
| — | the biased model assembled into a network state | `SocialNetwork.Bias.Profile` | ✅ |
| eq. (7) | generator `G̃` | `SocialNetwork.Bias.biasedGenerator` | ✅ |
| eq. (8) | `C_α^o` | `SocialNetwork.Bias.IsBiasedConsensus` | ✅ |
| eq. (9) | `L_α^o` | `SocialNetwork.Bias.IsBiasedLadder` | ✅ |
| Thm 4.1 | `α < 0`: all but one actor stop expressing, a.s. | `SocialNetwork.Bias.biasedAbsorption` | 🟡 |
| Thm 4.2 | `0 ≤ α < 1/(M-1)`: Thms 1, 2, 3 carry over | Thms 25, 27, 31 below | 🟡 |
| Rmk 2 | degeneracy for `α > 1/(M-1)` and `α ≥ 1 + 1/(M-1)` | `…pressure_lt_pressure_hear_of_neg`, `…le_pressure_hear_of_le_neg_one` | ✅ |

## Section 4 — Observables

| Paper | Statement | Lean | Status |
| --- | --- | --- | --- |
| §4 | public opinion `P_o (u) = ∑_a u (a, o)` | `SocialNetwork.publicOpinion` | ✅ |
| §4 | trust `T_a (u) = ∑_o u (a, o)` | `SocialNetwork.trust` | ✅ |
| Rmk 3 | `T_a ≡ 0` on `S` (no bias) | `SocialNetwork.IsState.trust_eq_zero` | ✅ |
| Rmk 3 | ↳ same statement in the biased model at `α = 0` | `…Memory.sum_pressure_eq_zero_of_bias_zero` | ✅ |

## Section 5 — Proofs

| Paper | Statement | Lean | Status |
| --- | --- | --- | --- |
| — | trajectories `(Aₙ, Oₙ)ₙ` and the states `U_{T_n}` | `SocialNetwork.Trajectory.state` | ✅ |
| — | `S` is preserved along a trajectory | `SocialNetwork.Trajectory.isState_state` | ✅ |
| Prop 5 | among `N` consecutive expressions one has `‖U(Aₙ,·)‖_∞ < N` | `SocialNetwork.exists_rowSup_actor_lt` | ✅ |
| — | ↳ growth bound `‖U_{T_m}(a₀,·)‖_∞ ≤ m` | `SocialNetwork.rowSup_state_le` | ✅ |
| — | ↳ no early expression comes from the null-row actor `a₀` | `…actor_ne_of_rowSup_state_zero` | ✅ |
| — | ↳ no actor expresses twice among the first `N` | `SocialNetwork.actor_ne_actor_of_lt` | ✅ |
| — | the greedy event `ξₙ^u` | `SocialNetwork.IsGreedyAt` | ✅ |
| Prop 6 | `⋂ ξ_j^u ⊆ {-MN < U_{T_N} < N}` | `SocialNetwork.entry_mem_of_greedy` | ✅ |
| — | ↳ sharp upper bound `U_{T_N} ≤ N - 1` | `SocialNetwork.entry_le_of_greedy` | ✅ |
| — | ↳ lower bound from the vanishing row sums | `SocialNetwork.neg_le_of_forall_le` | ✅ |
| Prop 7 | `⋂_{j≤(M+1)N} ξ_j^u ⊆ {U_{T_{(M+1)N}} ∈ L}` | `SocialNetwork.isLadder_state_of_greedy` | 🟡 |
| — | ↳ final step: from `C^o`, `N` greedy steps reach `L^o` | `SocialNetwork.isLadder_state` | ✅ |
| — | ↳ a greedy step in `C^o` expresses `o` | `SocialNetwork.opinion_eq_of_greedy` | ✅ |
| — | ↳ `C^o` is stable under expressing `o` | `SocialNetwork.IsConsensus.express` | ✅ |
| — | ↳ `C^o` carries a strictly positive entry (after Def 2) | `SocialNetwork.IsConsensus.exists_pos` | ✅ |
| — | ↳ no actor expresses twice in that window | `SocialNetwork.actor_ne_actor_of_greedy` | ✅ |
| — | ↳ the row of an actor that only listens to `o` | `SocialNetwork.state_add_of_hearing` | ✅ |
| — | ↳ `ξₙ^u` as a measurable subset of the sample space | `SocialNetwork.greedyEvent` | ✅ |
| — | ↳ its measurability (it is a cylinder) | `…measurableSet_greedyEvent` | ✅ |
| — | ↳ `⋂_{j≤n} ξⱼ^u` and its measurability | `…greedyEvents`, `…measurableSet_greedyEvents` | ✅ |
| Prop 5 | ↳ same statement on a sample point | `…exists_rowSup_actor_lt_ofPath` | ✅ |
| Prop 6 | ↳ same statement on the event `⋂ ξⱼ^u` | `…entry_mem_of_mem_greedyEvents` | ✅ |
| Prop 7 | ↳ final step on the event `⋂ ξⱼ^v` | `…isLadder_state_of_mem_greedyEvents` | ✅ |
| Prop 8 | `P(⋂_{j≤m} ξ_j^u) ≥ ζ_β^m` | `SocialNetwork.zeta_pow_le_pathMeasure_greedyEvents` | ✅ |
| Prop 8 | ↳ one-step bound `P(ξ₁^v) ≥ ζ_β`, uniform in `v` | `SocialNetwork.zeta_le_jumpPMF_argmaxFinset` | ✅ |
| Prop 8 | ↳ the induction step along `partialTraj` | `SocialNetwork.zeta_le_partialTraj_succ` | ✅ |
| Prop 8 | ↳ combined with Remark 4 | `SocialNetwork.one_sub_le_pathMeasure_greedyEvents` | ✅ |
| — | ↳ the maximum `y (v)` and that `Y (v) ≠ ∅` | `SocialNetwork.entrySup`, `…exists_entrySup` | ✅ |
| — | ↳ `ξₙ^u` says the expressed pair attains `y` | `SocialNetwork.isGreedyAt_iff_entrySup` | ✅ |
| — | ↳ gap estimate `v(b,o) - y(v) ≤ -1/(M-1)` | `SocialNetwork.le_entrySup_sub_one` | ✅ |
| Rmk 4 | `ζ_β` | `SocialNetwork.zeta`, `…zeta_pos`, `…zeta_le_one` | ✅ |
| Rmk 4 | `ζ_β ≥ 1 - M N e^{-β/(M-1)}` | `SocialNetwork.one_sub_le_zeta` | ✅ |
| Rmk 4 | `ζ_β^m ≥ 1 - m M N e^{-β/(M-1)}` (Bernoulli) | `SocialNetwork.one_sub_le_zeta_pow` | ✅ |
| Def 3 | skeleton transition kernel `Ũ^{β,u}` | `SocialNetwork.skeletonKernel` | ✅ |
| Def 3 | ↳ it is a Markov kernel | `…isMarkovKernel_skeletonKernel` | ✅ |
| Def 3 | ↳ carried by the states reachable by one `π^{a,o}` | `…skeletonKernel_reachable` | ✅ |
| Def 3 | ↳ `S` preserved with probability one | `…isState_skeletonKernel` | ✅ |
| Def 3 | ↳ law of `(Aₙ, Oₙ)ₙ` (Ionescu–Tulcea) | `SocialNetwork.pathMeasure` | ✅ |
| Def 3 | ↳ the process `Ũ_n^{β,u}`, and its measurability | `SocialNetwork.skeleton`, `…measurable_skeleton` | ✅ |
| Def 3 | ↳ the return time `R̃^{β,u} (θ)` | `SocialNetwork.returnTime` | ✅ |
| Def 3 | the invariant measure `μ̃^β` of the skeleton | `SocialNetwork.existsUnique_invariantSkeleton` | 🟡 |
| Def 4 | steep ladder sets `L̂^o`, `L̂` | `SocialNetwork.IsSteepLadder` | ✅ |
| Rmk 5 | `L ⊆ L̂` | `SocialNetwork.IsLadder.isSteepLadder` | ✅ |
| Rmk 5 | `{U_0(A₁,O₁) > 0} ⊆ {U_{T_1} ∈ L̂}` | `SocialNetwork.IsSteepLadder.express_of_pos` | ✅ |
| Rmk 5 | ↳ `L̂^o` is stable under expressing `o` | `SocialNetwork.IsSteepLadder.express` | ✅ |
| Rmk 5 | the bound `η` on `P(U_0(A₁,O₁) > 0)` | `SocialNetwork.eta_le_pathMeasure_positivePressure` | 🟡 |
| Prop 9 | `μ̃^β (u) ≤ C' e^{-β(N-1)}` for `u ∉ L̂` | `…measure_le_of_notMem_steepLadderSet` | 🟡 |
| Cor 10 | `μ̃^β (0) ≤ C'' e^{-β(N-1+1/(M-1))}` | `SocialNetwork.measure_zero_le` | 🟡 |
| Cor 11 | hitting-time corollary | `…tendsto_hittingTime_ladderSet_zero` | 🟡 |
| Prop 12 | the exponential-approximation criterion of [LM22] | `SocialNetwork.exitTime_approx_exponential` | 🟡 |
| Lem 13 | `P(R^{β,u}(L) > 2β) ≤ (M+1)²N² e^{-β/((M+1)N)}` | `SocialNetwork.probHittingGT_ladderSet_le` | 🟡 |
| Lem 14 | two-sided exit-time bounds (Appendix B) | `…le_probHittingGT_consensusOther`, `…probHittingLE_consensusOther_le` | 🟡 |
| Cor 15 | `c_β ≥ ½ N^{-3}(M+1)^{-3} e^{β/(M-1)}` | `SocialNetwork.le_characteristicTime` | 🟡 |
| Thm 16 | `α < 0`: non-explosion | `SocialNetwork.Bias.biasedNonExplosion` | 🟡 |
| Prop 17 | `P(U_{T_N}^{α,u} ∈ B_N^α) ≥ (NM)^{-N}` | `…measure_biasedBounded_ge` | 🟡 |
| Prop 18 | one actor expresses forever, with positive chance | `…inf_measure_forall_eq_first_pos` | 🟡 |

## Appendices

| Paper | Statement | Lean | Status |
| --- | --- | --- | --- |
| Def 5 | `S^o`, the matrices favouring `o` | `SocialNetwork.IsFavouring` | ✅ |
| Def 5 | the first-repeat time `τ(u)` | `SocialNetwork.firstRepeat` | ✅ |
| Def 5 | `τ(u) ∈ {2, …, N+1}` | `SocialNetwork.firstRepeat_le` | ✅ |
| — | actors before `τ(u)` are distinct | `SocialNetwork.actor_injOn_lt_firstRepeat` | ✅ |
| Lem 19 | `ξ^u_{τ(u)}` implies `Ũ_{τ(u)} ∈ ⋃_o S^o` | `…isFavouring_state_firstRepeat` | 🟡 (see below) |
| Lem 20 | `⋂ ξ_j` implies `Ũ ∈ C^o` for `u ∈ S^o` | `…isConsensus_state_of_favouring` | 🟡 (see below) |
| — | ↳ a greedy step in `S^o` expresses `o` (opening step) | `…opinion_eq_of_isMax_of_favouring` | ✅ |
| — | ↳ non-positive off-columns give `C^o` (closing step) | `SocialNetwork.isConsensus_of_nonpos` | ✅ |
| Prop 21–24 | biased analogues of Props 5–8 | `…exists_pressure_lt`, `…entry_mem_of_nearGreedy`, `…exists_horizon_isBiasedLadder`, `…biasedZeta_pow_le` | 🟡 |
| Thm 25 | biased analogue of Theorem 1 | `…existsUnique_biasedInvariant` | 🟡 |
| Prop 26 | biased analogue of Proposition 9 | `…biasedMeasure_le_of_notMem_steepLadder` | 🟡 |
| Rmk 8 | `max_p u(a,p) ≥ (M-1)α` for a non-null row | `SocialNetwork.Bias.le_max_pressure` | 🟡 |
| Thm 27 | biased analogue of Theorem 2 | `…biasedMeasure_ladderSet_ge`, `…tendsto_biasedHittingTime` | 🟡 |
| Lem 28, 29 | biased analogues of Lemmas 13, 14 | `…biasedProbHitting_le`, `…le_biasedProbHittingGT`, `…biasedProbHittingLE_le` | 🟡 |
| Cor 30 | biased analogue of Corollary 15 | `…le_biasedCharacteristicTime` | 🟡 |
| Thm 31 | biased analogue of Theorem 3 | `SocialNetwork.Bias.biasedMetastability` | 🟡 |

## Two points in Appendix A that the formalisation has to fill in

Neither of these affects the results of the paper — the conclusions of Lemmas 19 and 20
still appear to hold — but both are places where the written proof does not, as it stands,
compose into a Lean proof. They are recorded here because they are what currently blocks
those two entries above.

### Lemma 19: the `⌊m⌋ + 1` distinct actors

The proof writes "Therefore by (25), we obtain a sequence of `⌊m⌋ + 1` distinct actors
`{a₀, …, a_{⌊m⌋}} ⊂ {A₁, …, A_{τ(u)-1}}` … such that `Ũ_{τ(u)-1}(aⱼ, O_{τ(u)}) ≥ j + (m -
⌊m⌋)`" without giving the construction. A construction that works: read the actors
`A_{τ(u)-1}, A_{τ(u)-2}, …, A_i` backwards in time (where `A_i = A_{τ(u)}` is the repeated
actor). By (25) consecutive rows differ by exactly one expression, so their pressures for
`O_{τ(u)}` form a walk that starts at `0` — the actor `A_{τ(u)-1}` was just reset — ends at
`m`, and moves by `+1` when it passes an expression of `O_{τ(u)}` and by `-1/(M-1)`
otherwise. For each `j`, take the *first* time the walk reaches level `≥ j + r`. A first
passage can only happen on an up-step, which has size `1`, so the walk lands strictly below
`j + 1 + r`; the `⌊m⌋ + 1` first-passage times are therefore distinct, and they name
`⌊m⌋ + 1` distinct actors.

Separately, Definition 5 requires `n(u) = ⌊m⌋ ≥ 1`, i.e. `m ≥ 1`. The proof rules out
`m = 0` only through the case `τ(u) = 2`, but `m = 0` forces `Ũ_{τ(u)-1} = 0` for any
`τ(u)` (the maximum of a matrix with vanishing row sums is `0` only if the matrix is), so
the degenerate branch has to be taken on `m = 0` rather than on `τ(u) = 2`. The argument
given for `τ(u) = 2` covers it unchanged.

### Lemma 20: the induction invariant is not preserved by the reset row

The induction carries, for every `k`,

```
∀ a ∈ A, ∀ p ≠ o,    Ũₖ(a, p) ≤ n(u) + r - (k+1)/(M-1).
```

The actor that expresses at step `k` has its whole row reset to `0`, so its entries for
`p ≠ o` are exactly `0`. At the terminal `k = (M-1)(n(u)+1) - 1` the right-hand side is
`n(u) + r - (n(u)+1) = r - 1`, which lies in `[-1, 0)`. The invariant therefore asserts
`0 ≤ r - 1 < 0` for that actor.

The *conclusion* survives: membership in `C^o` only needs the off-columns to be `≤ 0`, and
`0` qualifies. Replacing the bound by `max(0, n(u) + r - (k+1)/(M-1))` gives an invariant
that is preserved (a reset row satisfies it outright, and a listening row decreases by
`1/(M-1)`), and still yields `≤ 0` at the terminal `k`.

A second point in the same induction: the invariant also asserts that `n(u)` witness actors
exist at every `k`. When the maximising actor is itself one of the witnesses — the typical
case — expressing resets it, and only `n(u) - 1` of the witnesses survive with their
pressures raised by `1`. The missing witness is replenished by the actors that have just
expressed, which accumulate pressure for `o` and form a staircase; that is the mechanism
already formalised in `SocialNetwork.isLadder_state`, but it is not the argument written in
the proof.

## What is stated but not proved

Every numbered statement of the paper is stated in Lean.  The proofs that are missing fall
into exactly three groups, and it is worth keeping them apart, because they are missing for
three different reasons.

### 1. Blocked on Mathlib (the 🟡 entries of Theorems 1, 2, 3, 4 and their auxiliaries)

Stated, unproved, and not provable today without first building library theory.  See
§"Infrastructure gaps" for what exactly is absent.

### 2. Blocked on the paper (Lemmas 19 and 20, hence Proposition 7)

Stated, unproved, and *not* blocked on Mathlib: the written proofs do not compose as they
stand.  See §"Two points in Appendix A".  Repairs are described there and appear to work; they
change the arguments rather than their presentation, so they are recorded rather than guessed
at.  Proposition 7 is 🟡 only because it is assembled from these two.

### 3. Routine, not formalised (four measurability lemmas and one arithmetic lemma)

Neither deep nor blocked, simply not done:

| Declaration | What is missing |
| --- | --- |
| `SocialNetwork.measurable_process` | `jumpCount` is a countable Boolean combination of the events `{Tₙ ≤ t}`; writing that out |
| `SocialNetwork.measurable_hittingTimeCts` | same, for the infimum over a countable dense set |
| `…Bias.measurableSet_biasedGreedyEvents`, `…Bias.measurableSet_nearGreedyEvents` | the cylinder argument of `SocialNetwork.measurableSet_greedyEvent`, transposed to profiles |
| `SocialNetwork.Bias.sum_ge_of_injective` | `N` distinct naturals sum to at least `0+1+⋯+(N-1)` |

The last is worth a note as a **Mathlib gap in its own right**: there is no lemma to this
effect, and none from which it follows in one step.  The natural route is
`Finset.orderEmbOfFin` plus "a strictly monotone `Fin N → ℕ` dominates the identity", but
`StrictMono.le_apply` (`Mathlib/Order/WellFounded.lean:248`) is stated only for endomorphisms
`f : β → β`, so the `Fin N → ℕ` case has to be redone by hand.

## Infrastructure gaps

This section states, with exact Mathlib names, what the library provides and what it does
not.  It was rewritten against the sources of the pinned revision
(`lake-manifest.json`, Mathlib `v4.33.0` = `db584cd6`); do not trust it against a different
revision without re-checking.

### Resolved: the construction of the process, in discrete *and* continuous time

The first draft of this blueprint listed "construction of the process from a generator" as the
principal gap.  It is not one.

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

### Still missing, in DISCRETE time

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

### Still missing, in CONTINUOUS time

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

### Which theorems depend on which

Theorems 2 and 3 are, in the paper's own architecture, statements about the **skeleton**: the
continuous-time versions follow from the discrete ones through the transfer (13) and the
control of the holding times.  So they are blocked by items 1–5, not by 7.  Only Theorem 1.1 —
and its biased twin Theorem 16 — genuinely needs the continuous-time item 7.

The shortest path to Theorem 2 is therefore: Doeblin ⇒ unique invariant measure for a
countable-state kernel (item 1), then Kac (item 4), then Proposition 9 follows from
Proposition 7, Remark 5 and the bound of Proposition 8 that is already proved
(`SocialNetwork.zeta_pow_le_pathMeasure_greedyEvents`), and Theorem 2.1 follows from
Proposition 9 by (13).


## A definition corrected: `IsSteepLadder`

Definition 4 reads

```
L̂^o = {u ∈ S : u (a, o) ∈ ℤ ∀ a;   0 = u (a₁, o) < u (a₂, o) < … < u (a_N, o), {a₁,…,a_N} = A;
        and ∀ p ≠ o, u (a, p) = -u (a, o)/(M-1)}.
```

The chain `0 = u (a₁, o) < …` says two things: the values are pairwise distinct, **and** the
smallest of them is `0`, so the whole column is non-negative.  The first version of
`SocialNetwork.IsSteepLadder` recorded only "pairwise distinct" and "some value is `0`", which
is strictly weaker — and the missing sign condition is not recoverable from the others, since
`∑_p u (a, p) = 0` holds identically once `other` does, whatever the sign of `u (a, o)`.

`IsSteepLadder` now carries the field `nonneg : ∀ a, 0 ≤ u a o`.  This costs nothing
elsewhere: the only place that builds an `IsSteepLadder` is `IsLadder.isSteepLadder`, and the
field is supplied by the already-proved `IsLadder.nonneg`.  It is what makes Remark 5
(`SocialNetwork.IsSteepLadder.express_of_pos`) true.

## A second correction: equation (6) is not stable

Equation (6) pins down `S^α` by two conditions on the memory profile: some actor has heard
nothing since it last expressed, and `∑_a nₐ ≥ N(N-1)/2`.  Remark 1 asserts that `S^α` is
stable under every `π_α^{a,o}`.

**The second condition is not stable.**  Expressing sets the expresser's `nₐ` to `0` and adds
one to every other, so the sum changes by `(N-1) - nₐ`, which is negative as soon as the
expressing actor had heard more than `N-1` expressions.  For `N = 3`, where the threshold is
`3`, the profile `n = (0, 0, 3)` has sum `3` and satisfies the condition; expressing from the
third actor gives `n = (1, 1, 0)`, of sum `2`.

The paper's own justification for the condition proves something stronger, and the stronger
statement *is* stable: "the actors cannot express simultaneously", so the `nₐ` are the times
elapsed since `N` distinct moments and are therefore **pairwise distinct**.  Expressing
replaces `{n_b : b ≠ a}` by `{n_b + 1 : b ≠ a}`, all at least one, and adds `nₐ ↦ 0`, so
distinctness survives.  Distinctness plus a null row gives `∑_a nₐ ≥ 0 + 1 + ⋯ + (N-1)`, so
nothing is lost.

`SocialNetwork.Bias.IsBiasedState` therefore takes distinctness as its second field, and the
paper's inequality is derived from it
(`SocialNetwork.Bias.IsBiasedState.two_mul_totalHeard_ge`, stated as `N(N-1) ≤ 2 ∑ₐ nₐ` to
avoid the division).  Stability, `SocialNetwork.Bias.IsBiasedState.express`, is proved.

As with the two points of Appendix A, this changes no result of the paper: every state the
process actually visits has distinct `nₐ`, which is the regime Remark 1 is describing.


## Immediate next steps

The deterministic layer is complete, every numbered statement is stated, and the discrete-time
probabilistic layer is built.  In rough order of cost:

1. **The four routine measurability lemmas and `sum_ge_of_injective`** listed in §"What is
   stated but not proved", item 3.  None needs new theory; together they are a day's work and
   they remove the only `sorry`s in this development that are nobody's fault.
2. **The bound `η` of Remark 5** (`SocialNetwork.eta_le_pathMeasure_positivePressure`).  The
   arithmetic is available through `SocialNetwork.jumpPMF_apply`; what is missing is the
   comparison showing that the worst case over `L̂` is attained on `L`.  This is the first
   genuinely mathematical item that is neither blocked on Mathlib nor on the paper.
3. **Remark 8** (`SocialNetwork.Bias.le_max_pressure`).  The pigeonhole step is done
   (`SocialNetwork.Bias.exists_count_ge`); what remains is the arithmetic of the paper's
   decomposition `nₐ = (k-1)M + r`.
4. **Lemmas 19 and 20**, with the repairs of §"Two points in Appendix A".  Worth settling with
   the authors first, since the repairs change the written proofs.  Proposition 7 then follows
   by assembling them with `SocialNetwork.isLadder_state`.
5. **Doeblin ⇒ unique invariant measure for a countable-state Markov kernel.**  This is the
   keystone: Theorem 1.2, Definition 3's `μ̃^β`, and through them Theorems 2, 3, 25, 27 and 31
   all wait on it.  It is a self-contained piece of library work, of independent value, and
   it does not depend on anything else in this list.
6. **Kac's lemma** for a countable-state chain.  Needed by Proposition 9 and by nothing else
   here.
7. **Poisson point processes and the superposition comparison**, for Theorems 1.1 and 16.
   The largest item, and the one the fewest results depend on.

Items 5, 6 and 7 are Mathlib contributions rather than contributions to this repository.
