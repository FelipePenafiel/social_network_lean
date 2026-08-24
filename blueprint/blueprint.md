# Blueprint — arXiv:2607.19651

*Metastability and phase transition in a social network model with multiple opinions*,
Felipe Peñafiel, Kádmo Laxa.

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
| eq. (3) | generator `G` of the jump process | — | 🚧 |
| Thm 1.1 | non-explosion, `P(sup Tₘ = ∞) = 1` | — | 🚧 |
| Thm 1.2 | existence and uniqueness of `μ^β` | — | 🚧 |
| Def 1 | ladder sets `L^o`, `L` | `SocialNetwork.IsLadder` | ✅ |
| Thm 2.1 | `μ^β (L) ≥ 1 - C e^{-β/(M-1)}` | — | 🚧 |
| Thm 2.2 | hitting time of `L` vanishes as `β → ∞` | — | 🚧 |
| Def 2 | consensus sets `C^o`, `C^{-o}` | `SocialNetwork.IsConsensus` | ✅ |
| — | `L^o ⊆ C^o` | `SocialNetwork.IsLadder.isConsensus` | ✅ |
| Thm 3 | metastability: `R^{β,u}(C^{-o})/E[·] → Exp(1)` | — | 🚧 |

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
| Prop 7 | `⋂_{j≤(M+1)N} ξ_j^u ⊆ {U_{T_{(M+1)N}} ∈ L}` | — | ⬜ |
| Prop 8 | `P(⋂_{j≤m} ξ_j^u) ≥ ζ_β^m` | — | 🚧 |
| — | ↳ gap estimate `v(b,o) - y(v) ≤ -1/(M-1)` | — | ⬜ |
| Rmk 4 | `ζ_β^m ≥ 1 - m M N e^{-β/(M-1)}` (Bernoulli) | — | ⬜ |
| Def 3 | skeleton process `Ũ^{β,u}`, `μ̃^β`, `R̃^{β,u}` | — | 🚧 |
| Def 4 | steep ladder sets `L̂^o`, `L̂` | `SocialNetwork.IsSteepLadder` | ✅ |
| Rmk 5 | `L ⊆ L̂` | `SocialNetwork.IsLadder.isSteepLadder` | ✅ |
| Rmk 5 | `{U_0(A₁,O₁) > 0} ⊆ {U_{T_1} ∈ L̂}`, bound `η` | — | 🚧 |
| Prop 9 | `μ̃^β (u) ≤ C' e^{-β(N-1)}` for `u ∉ L̂` | — | 🚧 |
| Cor 10 | `μ̃^β (0) ≤ C'' e^{-β(N-1+1/(M-1))}` | — | 🚧 |
| Cor 11 | hitting-time corollary | — | 🚧 |
| Prop 12 | coupling / regeneration estimate for `o` fixed | — | 🚧 |
| Lem 13 | — | — | 🚧 |
| Lem 14 | (proved in Appendix B) | — | 🚧 |
| Cor 15 | — | — | 🚧 |
| Thm 16 | `α < 0`: absorption | — | 🚧 |
| Prop 17 | — | — | 🚧 |
| Prop 18 | sequence of expressing actors `(Aₙ^u)` | — | 🚧 |

## Appendices

| Paper | Statement | Lean | Status |
| --- | --- | --- | --- |
| Def 5 | `S^o`, the matrices favouring `o` | — | ⬜ |
| Lem 19 | `ξ^u_{τ(u)}` implies … | — | ⬜ |
| Lem 20 | `⋂ ξ_j` implies … for `u ∈ S^o` | — | ⬜ |
| Prop 21–24 | biased analogues of Props 5–8 | — | ⬜ / 🚧 |
| Thm 25 | biased analogue of Theorem 1 | — | 🚧 |
| Prop 26 | biased analogue of Proposition 9 | — | 🚧 |
| Rmk 8 | row structure for `0 < α < 1/(M-1)` | — | ⬜ |
| Thm 27 | biased analogue of Theorem 2 | — | 🚧 |
| Lem 28, 29 | biased analogues of Lemmas 13, 14 | — | 🚧 |
| Cor 30 | biased analogue of Corollary 15 | — | 🚧 |
| Thm 31 | biased analogue of Theorem 3 | — | 🚧 |

## Infrastructure gaps

The statements marked 🚧 are not blocked by the difficulty of the paper's arguments but by
missing library support. Mathlib currently has no theory of **continuous-time Markov jump
processes on a countable state space**. Concretely, the following are prerequisites and do
not exist in usable form today:

1. **Construction of the process from a generator.** Given jump rates `q (u, v)` on a
   countable set, build the jump chain / holding time representation and the associated
   process `(U_t)`. Needed for eq. (3) and eq. (7).
2. **Non-explosion criteria.** Theorem 1.1 is proved by sandwiching the jump times between
   two Poisson processes; Mathlib has Poisson point processes but not the comparison
   machinery for jump-time superpositions.
3. **Invariant measures and Doeblin's condition.** The proof of Theorem 1.2 establishes a
   uniform minorisation and concludes uniform ergodicity of the skeleton chain, then
   transfers the invariant measure to continuous time via `μ ∝ μ̃ / q`. Mathlib has
   `MeasureTheory.Measure.IsInvariant`-style notions but not the Doeblin ⇒ unique
   invariant measure theorem for countable chains.
4. **Kac's lemma**, used in Proposition 9 to convert `1/μ̃^β (u)` into an expected return
   time.
5. **Convergence in distribution to `Exp(1)`** with quantitative Kolmogorov-type bounds, as
   in Theorem 3.

A realistic route is therefore to formalise the deterministic and combinatorial layer
first (Section 2's state space, the ladder/consensus geometry, Propositions 5–7 and the
Appendix A lemmas, which are statements about *trajectories* and not about their
probabilities), then build the missing chain infrastructure, then close the probabilistic
statements. The trajectory-level statements are the bulk of the paper's combinatorial
content and are formalisable today.

## Immediate next steps

1. ~~Model a trajectory as the data `(Aₙ, Oₙ)ₙ` and iterate `express`.~~ Done
   (`SocialNetwork.Trajectory`).
2. ~~Prove Proposition 5 (pigeonhole).~~ Done (`SocialNetwork.exists_rowSup_actor_lt`).
3. ~~Define the greedy event `ξₙ^u`.~~ Done (`SocialNetwork.IsGreedyAt`).
4. ~~Prove Proposition 6.~~ Done (`SocialNetwork.entry_mem_of_greedy`).
5. Prove Proposition 7 via Appendix A (Definition 5 and Lemmas 19, 20): `(M+1)N` greedy
   steps land in `L`.
6. Assemble the biased model into a network state (one `Memory` per actor) and close the
   remaining ⬜ entries of Section 3: `u (a, p) ∈ ℤ + γℤ`, and `0 ∉ S^α` when
   `(M-1) α ≠ 0`.
7. Prove the gap estimate behind Proposition 8: on the state space, two distinct entries
   differ by at least `1` in scaled coordinates. The probabilistic conclusion then waits on
   the infrastructure above, but the arithmetic half does not.
