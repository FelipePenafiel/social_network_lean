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

What is formalised today is the **deterministic layer** together with the **discrete-time
probabilistic layer**.

Deterministic: the state space, the expression operator, the conservation law that makes the
state space stable, the ladder/consensus geometry of Definitions 1, 2 and 4, the biased model
of Section 3 through its variable-length memory, **Propositions 5 and 6**, the final step of
Proposition 7 (from a consensus state, `N` greedy expressions reach a ladder), the
deterministic half of Remark 5, and the vocabulary of Appendix A.

Probabilistic: the **skeleton process of Definition 3** — the jump rates of equation (3), the
transition kernel `Ũ^{β,u}`, the law of the sequence `(Aₙ, Oₙ)ₙ` built by Ionescu-Tulcea, the
process `Ũ_n` and the return time `R̃^{β,u}` — and **Proposition 8**, `P(⋂ ξⱼ^u) ≥ ζ_β^m`,
with Remark 4's Bernoulli bound. The chain is driven by the expressed pairs rather than by the
matrices, so a sample point *is* a `Trajectory` and Propositions 5, 6 and 7 apply to a
realisation pointwise, with no almost-sure qualifier.

Two points in the written proofs of Lemmas 19 and 20 do not compose into Lean proofs as
they stand; the blueprint states both precisely, along with repairs that appear to work.
Neither affects the paper's results.

Theorems 1 to 4 are **not** formalised. In continuous time nothing is: Mathlib has no theory
of Markov jump processes on a countable state space. In discrete time — which is where
Theorems 2 and 3 essentially live — what is missing is Doeblin's condition (hence the
existence and uniqueness of the skeleton's invariant measure `μ̃^β`) and Kac's lemma.
`blueprint/blueprint.md` lists every numbered statement of the paper, its Lean counterpart if
there is one, and, for the ones that are blocked, which piece of missing infrastructure blocks
it, with exact Mathlib names.

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
SocialNetwork/Skeleton.lean   Definition 3: rates of eq. (3), Ũ^{β,u}, the law of (Aₙ,Oₙ)ₙ
SocialNetwork/Greedy.lean     Proposition 8
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
