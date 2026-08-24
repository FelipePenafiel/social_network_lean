# Blueprint — arXiv:2607.19651

*Metastability and phase transition in a social network model with multiple opinions*,
Felipe Penafiel, Kádmo Laxa.

This file is the working map between the numbered statements of the paper and their Lean
counterparts. Every statement of the paper appears here, whether or not it has been
formalised, so that the gap between the article and the repository is always explicit.

Status legend:

| Symbol | Meaning |
| --- | --- |
| ✅ | Stated **and** proved in Lean, no `sorry` |
| 🟡 | Stated in Lean, proof contains `sorry` |
| ⬜ | Not yet stated in Lean |
| 🚧 | Blocked on missing Mathlib infrastructure (see §"Infrastructure gaps") |

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
| Rmk 1 | `u (a, p) ∈ ℤ + γℤ` | — | ⬜ |
| Rmk 1 | a row is null if `nₐ = 0` | `…Memory.pressure_eq_zero_of_heard_eq_zero` | ✅ |
| Rmk 1 | … and only if, when `(M-1) α ≠ 0`; hence `0 ∉ S^α` | — | ⬜ |
| — | the biased model assembled into a network state | — | ⬜ |
| eq. (7) | generator `G̃` | — | 🚧 |
| eq. (8) | `C_α^o` | — | ⬜ |
| eq. (9) | `L_α^o` | — | ⬜ |
| Thm 4.1 | `α < 0`: all but one actor stop expressing, a.s. | — | 🚧 |
| Thm 4.2 | `0 ≤ α < 1/(M-1)`: Thms 1, 2, 3 carry over | — | 🚧 |
| Rmk 2 | degeneracy for `α > 1/(M-1)` and `α ≥ 1 + 1/(M-1)` | — | ⬜ |

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
| Thm 16 | `α < 0`: absorption | — | 🚧 |
| Prop 17 | — | — | 🚧 |
| Prop 18 | sequence of expressing actors `(Aₙ^u)` | — | 🚧 |

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
| Prop 21–24 | biased analogues of Props 5–8 | — | ⬜ / 🚧 |
| Thm 25 | biased analogue of Theorem 1 | — | 🚧 |
| Prop 26 | biased analogue of Proposition 9 | — | 🚧 |
| Rmk 8 | row structure for `0 < α < 1/(M-1)` | — | ⬜ |
| Thm 27 | biased analogue of Theorem 2 | — | 🚧 |
| Lem 28, 29 | biased analogues of Lemmas 13, 14 | — | 🚧 |
| Cor 30 | biased analogue of Corollary 15 | — | 🚧 |
| Thm 31 | biased analogue of Theorem 3 | — | 🚧 |

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

## Infrastructure gaps

This section states, with exact Mathlib names, what the library provides and what it does
not.  It was rewritten against the sources of the pinned revision
(`lake-manifest.json`, Mathlib `v4.33.0` = `db584cd6`); do not trust it against a different
revision without re-checking.

The headline change since the first draft of this blueprint is that **the discrete-time
construction is no longer a gap**.  Mathlib now proves the Ionescu-Tulcea theorem, and proves
it for arbitrary measurable spaces.

### Resolved in discrete time: constructing the process (was gap 1)

`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` provides

```lean
ProbabilityTheory.Kernel.traj (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (a : ℕ) : Kernel (Π i : Finset.Iic a, X i) (Π n, X n)
ProbabilityTheory.Kernel.trajMeasure (μ₀ : Measure (X 0)) (κ) : Measure (Π n, X n)
```

together with `instance : IsMarkovKernel (traj κ a)`, the projections
`traj_map_frestrictLe`, `map_traj_succ_self`, the uniqueness statement `eq_traj`, the
composition `traj_comp_partialTraj`, and integration lemmas (`lintegral_traj`,
`integral_traj`, `condExp_traj`).  The finite-horizon kernels are
`ProbabilityTheory.Kernel.partialTraj` in `IonescuTulcea/PartialTraj.lean`.

Two points make this directly usable here:

* **No standard-Borel hypothesis.**  The only assumption on the state spaces is
  `[∀ n, MeasurableSpace (X n)]`.  (Only `condDistrib_trajMeasure` needs
  `StandardBorelSpace`, and nothing here uses it.)
* **The kernels may depend on the whole past**, which is what lets the chain be driven by the
  expressed pairs `(Aₙ, Oₙ)` rather than by the matrices — see `SocialNetwork/Skeleton.lean`.
  That choice is what makes Propositions 5, 6 and 7 transfer to the probabilistic setting
  *pointwise*, with no almost-sure clause.

Supporting API used in `SocialNetwork/Skeleton.lean`:
`ProbabilityTheory.Kernel.ofFunOfCountable` (every function out of a countable space with
measurable singletons is a kernel), `PMF.normalize`, `PMF.map`, `PMF.toMeasure` with
`PMF.toMeasure.isProbabilityMeasure`, `ProbabilityTheory.Kernel.comap` with
`IsMarkovKernel.comap`, the `Monoid (Kernel α α)` instance and the Chapman-Kolmogorov
equations `ProbabilityTheory.Kernel.pow_add` and `pow_succ_apply_eq_lintegral`.

Note that **no bridge `PMF → Kernel` exists**: `Mathlib/Probability/Kernel/` never mentions
`PMF`.  Going through `PMF.toMeasure` and `Kernel.ofFunOfCountable` is three lines, but it is
not library API.

Measurability costs nothing here.  `Pressure N M = Actor N → Opinion M → ℤ` is `Countable`
(`instance [Finite α] [∀ a, Countable (π a)] : Countable (∀ a, π a)`) and satisfies
`MeasurableSingletonClass` (`Pi.instMeasurableSingletonClass`, `Int.instMeasurableSpace = ⊤`),
so `MeasurableSingletonClass.toDiscreteMeasurableSpace` applies and *every* subset is
measurable, *every* function measurable (`MeasurableSet.of_discrete`, `Measurable.of_discrete`).
The same holds for `Jump N M` and for every space of finite histories.

### Still missing in DISCRETE time

These are what block Theorem 1.2, Proposition 9 and Corollaries 10 and 11 even though those
statements live entirely on the skeleton.

1. **Doeblin's condition ⇒ a unique invariant measure.**  `Kernel.Invariant κ μ := μ.bind κ = μ`
   exists in `Mathlib/Probability/Kernel/Invariance.lean`, together with `Invariant.comp`,
   `IsReversible` and `IsReversible.invariant` — and that is the entire file.  There is no
   existence statement, no uniqueness statement, no convergence statement, and no file in
   Mathlib uses `Kernel.Invariant`.  A search of the whole library for `Doeblin`,
   `minorisation` and `minorization` returns nothing, and there is no total-variation distance
   between measures (`totalVariation` exists only for signed and vector measures, as part of
   the Jordan decomposition).  So even the existence of `μ̃^β` for a finite-state chain has to
   be built from scratch.
2. **Irreducibility has a definition but no theory.**
   `ProbabilityTheory.Kernel.IsIrreducible (φ : Measure α) (κ : Kernel α α)` exists in
   `Mathlib/Probability/Kernel/Irreducible.lean` (Meyn–Tweedie 4.2.1(ii)), but the file
   contains only the class, two trivial instances, and `isIrreducible_of_le_measure`.  Nothing
   connects it to invariant measures or to recurrence.
3. **Kac's lemma**, used in Proposition 9 to turn `1/μ̃^β (u)` into `E [R̃^{β,u} (u)]`.  Absent:
   a search for `Kac` finds only Kac–Moody algebras, and there is no `returnTime` anywhere.
   `Mathlib/Dynamics/Ergodic/Conservative.lean` has Poincaré recurrence, but for a single
   measure-preserving *map*, which does not apply to a kernel.
4. **Recurrence for Markov chains**: nothing.  `Mathlib/Dynamics/Ergodic/` is entirely about
   maps, not kernels.
5. **Quantitative convergence to `Exp(1)`** (Theorem 3).  `TendstoInDistribution` now exists
   (`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`, with the continuous
   mapping theorem and Slutsky), and `Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean`
   metrises weak convergence, so the *qualitative* statement is now expressible.  The
   Kolmogorov-type quantitative bound the paper proves is not.

What is available on the stopping-time side: `MeasureTheory.hittingAfter` and
`MeasureTheory.hittingBtwn` (`Mathlib/Probability/Process/HittingTime.lean` — note the rename
from the older `hitting`), `MeasureTheory.IsStoppingTime`, `stoppedProcess`,
`Filtration.natural`.  `SocialNetwork.returnTime` is `hittingAfter` applied to the skeleton.
Showing it is a stopping time needs a filtration on the path space; `Filtration.natural` wants
`StronglyMeasurable`, hence a topology on the state space, so it would have to be built by
hand.  Nothing below depends on it.

### Still missing in CONTINUOUS time

6. **Construction of the jump process from a generator.**  Given the rates
   `q (u, v)` of equation (3) on a countable set, build the jump-chain / holding-time
   representation and the process `(U_t)`.  Mathlib has no such construction, and no theory of
   continuous-time Markov jump processes at all.  This is what blocks eq. (3)'s generator and
   eq. (7).
7. **Non-explosion** (Theorem 1.1).  The paper sandwiches the jump times between two Poisson
   processes.  **Mathlib has no Poisson point process**: `Mathlib/Probability/Distributions/`
   `Poisson/` contains the Poisson *distribution on `ℕ`* (`poissonMeasure`) and the Poisson
   limit theorem, nothing more.  (An earlier draft of this blueprint claimed Mathlib had
   Poisson point processes; that was wrong.)
8. **Transfer of the invariant measure**, `μ^β (u) ∝ μ̃^β (u) / q^β (u)` of equation (13), and
   the bijection between the stationary laws of the two processes.  This needs 6 first.

### Why this matters less than it looks

Theorems 2 and 3 live essentially on the **skeleton**: Theorem 2 is proved by first proving
its analogue for `μ̃^β` (Proposition 9 and Corollaries 10, 11), and Theorem 3's regeneration
argument (Propositions 12, 17, 18, Lemmas 13, 14) is a statement about the sequence of
expressed pairs.  So the continuous-time gaps 6–8 do **not** block them; the discrete-time
gaps 1–3 do.  Concretely, the shortest path to Theorem 2 is:

> Doeblin ⇒ existence and uniqueness of `μ̃^β` (gap 1) → Kac (gap 3) → Proposition 9 → Theorem 2.

Everything on that path is a statement about a **finite-state** chain, since `S` intersected
with the reachable set from any `u ∈ S` is finite once the entries are bounded, and the
minorisation the paper establishes is uniform.  None of it needs continuous time.

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

## Immediate next steps

1. ~~Model a trajectory as the data `(Aₙ, Oₙ)ₙ` and iterate `express`.~~ Done
   (`SocialNetwork.Trajectory`).
2. ~~Prove Proposition 5 (pigeonhole).~~ Done (`SocialNetwork.exists_rowSup_actor_lt`).
3. ~~Define the greedy event `ξₙ^u`.~~ Done (`SocialNetwork.IsGreedyAt`), and it is now also a
   measurable subset of the sample space (`SocialNetwork.greedyEvent`).
4. ~~Prove Proposition 6.~~ Done (`SocialNetwork.entry_mem_of_greedy`).
5. ~~Build the skeleton of Definition 3.~~ Done (`SocialNetwork/Skeleton.lean`): the rates of
   equation (3), the transition kernel `Ũ^{β,u}` with `IsMarkovKernel`, the law of
   `(Aₙ, Oₙ)ₙ` by Ionescu-Tulcea, the process `Ũ_n` and the return time `R̃^{β,u}`.
6. ~~Prove the gap estimate behind Proposition 8 and the Bernoulli bound of Remark 4.~~ Done
   (`SocialNetwork.le_entrySup_sub_one`, `SocialNetwork.one_sub_le_zeta_pow`).
7. **Finish Proposition 8.**  This is now the first thing that is neither done nor blocked on
   missing infrastructure.  It splits in two:
   * the one-step bound `P (ξ₁^v) ≥ ζ_β` for every `v ∈ S`, which is the paper's computation
     `|Y(v)| e^{βy} / (|Y(v)| e^{βy} + ∑_{v(b,o)<y} e^{βv(b,o)})` bounded below using
     `|Y(v)| ≥ 1`, the gap estimate (done), and `|A × O| = MN`.  Everything it needs is in
     place; it is a finite computation with `Finset.sum` over `Jump N M`.
   * the iteration `P (⋂_{j≤m} ξⱼ^u) ≥ ζ_β^m`, by induction along
     `ProbabilityTheory.Kernel.partialTraj` using `partialTraj_succ_eq_comp` and the
     composition-product lemmas of `Kernel/Composition/CompProd.lean`.
8. Finish Proposition 7: the bodies of Lemmas 19 and 20, which need the repairs described
   above — the first-passage construction for Lemma 19, and the weakened invariant
   `max(0, n(u) + r - (k+1)/(M-1))` together with the staircase replenishment for Lemma 20.
   Worth settling with the authors before formalising, since the repairs change the written
   proofs rather than just their presentation.
9. The bound `η` of Remark 5, `P (U_0 (A₁, O₁) > 0) ≥ η` for `u ∈ L`: another finite
   computation with the rates, now that the deterministic half of Remark 5 is proved.
10. Assemble the biased model into a network state (one `Memory` per actor) and close the
    remaining ⬜ entries of Section 3: `u (a, p) ∈ ℤ + γℤ`, and `0 ∉ S^α` when
    `(M-1) α ≠ 0`.
11. Everything past that — Theorem 1.2, Proposition 9, Corollaries 10 and 11, Theorem 2,
    Theorem 3 — waits on Doeblin and Kac, in that order.  See "Infrastructure gaps".
