# social_network_lean

A Lean 4 / Mathlib formalisation of

> **Metastability and phase transition in a social network model with multiple opinions**
> Felipe Penafiel, Kádmo Laxa — [arXiv:2607.19651](https://arxiv.org/abs/2607.19651)

The paper studies a stochastic opinion dynamics model on a fully connected network of
`N ≥ 3` actors expressing opinions from a set of `M ≥ 2` opinions. Each actor carries an
`M`-tuple of *social pressures*; the matrix of all social pressures evolves as a Markov
jump process whose rates grow exponentially with the pressure, modulated by a polarization
coefficient `β`. Expressing an opinion resets the speaker's row and shifts everybody
else's. The results are fast consensus formation, existence and uniqueness of an invariant
measure, metastability as `β → ∞`, and — on introducing a communication bias `α` — a phase
transition at `α = 0`.

## Status

The **deterministic layer** of the paper is formalised and proved: the state space, the
expression operator and the conservation law behind it, the ladder/consensus geometry of
Definitions 1, 2 and 4, Propositions 5 and 6, the final step of Proposition 7, and the
vocabulary of Appendix A.

The **discrete-time probabilistic layer** is built and proved: the jump rates of equation (3),
the skeleton kernel of Definition 3 as a `Kernel (Pressure N M) (Pressure N M)`, the law of a
realisation via Mathlib's Ionescu–Tulcea theorem, the greedy events `ξₙ^u` as measurable sets,
and **Proposition 8** with Remark 4.

The **continuous-time process** is built — the jump-hold representation is a discrete-time
chain carrying one real coordinate, so `Kernel.traj` constructs it — and with it the jump
times, the process `U_t`, the transition semigroup and the hitting times `R^{β,u}(θ)`.

The **biased model of Section 3** is assembled: memory profiles, the operator `π_α^{a,o}`, the
state space `S^α`, the generator `G̃` of equation (7), the sets of equations (8) and (9), and
the biased skeleton and process.

**Every numbered statement of the paper is now stated in Lean.**  The ones whose proofs are not
formalised carry a `sorry` and are marked 🟡 in the blueprint.  They are unproved for three
distinct reasons, which the blueprint keeps apart: blocked on missing Mathlib theory (Doeblin's
criterion, Kac's lemma, Poisson point processes), blocked on the paper (Lemmas 19 and 20, whose
written proofs do not compose — repairs are recorded), or simply routine and not yet done (four
measurability lemmas and one arithmetic lemma).

The library is **not** `sorry`-free, by design.  What CI enforces instead is that no
declaration listed as complete in `.github/workflows/ci.yml` depends on `sorryAx`; every run
also prints an inventory of the outstanding `sorry`s.

Formalising surfaced three places where the paper needs correcting, none of which affects its
results.  Two are in Appendix A (Lemmas 19 and 20); the third is that the second condition of
equation (6) is not stable under `π_α^{a,o}`, though the justification the paper gives for it
proves a stronger condition that is.  All three are stated precisely in the blueprint.

Read the blueprint before adding anything: it is the contract between the paper and the
repository.

## Scaled coordinates

The paper's matrices have entries in `ℤ + (1/(M-1))ℤ`. Everything here is stated for the
rescaled matrix `v (a, o) := (M - 1) * u (a, o)`, which is an *integer* matrix. Under this
rescaling the operator of equation (1) adds `M - 1` on the expressed column and subtracts
`1` on the others. The rescaling is a bijection, so no statement changes, and the
arithmetic of the paper becomes plain integer arithmetic — in particular the estimate
behind Proposition 8, that two distinct entries differ by at least `1/(M-1)`, becomes the
statement that two distinct integers differ by at least `1`.

## Layout

```
SocialNetwork.lean            root module
SocialNetwork/Defs.lean       pressure matrices, π^{a,o}, trust, public opinion, S
SocialNetwork/Ladder.lean     ladder sets L^o, consensus sets C^o, steep ladders L̂^o
SocialNetwork/Trajectory.lean realisations (Aₙ, Oₙ)ₙ and the deterministic layer of §5
SocialNetwork/Consensus.lean  greedy dynamics from a consensus state reach a ladder
SocialNetwork/Favouring.lean  Definition 5, the first-repeat time τ(u), Appendix A pieces
SocialNetwork/Bias.lean       §3, via the variable-length memory (nₐ, cₚ) of eq. (6)
SocialNetwork/Skeleton.lean   Definition 3: jump rates, skeleton kernel, law of a realisation
SocialNetwork/Greedy.lean     Proposition 8 and Remark 4
SocialNetwork/Appendix.lean   Appendix A: Proposition 7, Lemmas 19 and 20, Remark 5, Prop 9
SocialNetwork/ContinuousTime.lean  eq. (3), the jump process, Theorems 1, 2, 3
SocialNetwork/BiasedModel.lean     §3 assembled: S^α, C_α^o, L_α^o, Remarks 1, 2, 8
SocialNetwork/BiasedResults.lean   §3 and Appendix C: Theorems 4, 16, 25, 27, 31
blueprint/blueprint.md        paper ↔ Lean correspondence and status of every statement
```

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned in
`lean-toolchain` and Mathlib is pinned in `lake-manifest.json`.

```sh
lake exe cache get   # download Mathlib's prebuilt .olean files (do not skip)
lake build
```

`lake exe cache get` is not optional in practice: without it, Lean rebuilds Mathlib from
source, which takes hours.

## Contributing

Two rules:

1. Every new declaration that corresponds to a numbered statement of the paper cites it in
   its docstring (`Proposition 5`, `eq. (6)`, …), and the blueprint table is updated in the
   same commit.
2. A definition must be readable against the paper. Where a reformulation is used for
   convenience — as with the scaled coordinates, or with `(M - 1) * u a p = - u a o`
   standing for `u (·, p) = - u (·, o) / (M - 1)` — say so in the docstring.

## Licence

Apache 2.0.
