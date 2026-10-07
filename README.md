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

## Where things stand

Every numbered statement and displayed equation of the paper — 60 of them — is stated in
Lean. All are proved, except three statements and the results whose proofs go through
them.

* **Lemma 20** (Appendix A). As printed it is false for `M ≥ 4`; see
  [`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) §1.1. Proposition 7 is written from it, and
  through Proposition 7 so are Proposition 9, Corollaries 10 and 11, Lemma 13 and
  Theorems 2 and 3.
* **Proposition 23** (Appendix C), whose proof the paper gives as that of Proposition 7,
  through biased analogues of Lemmas 19 and 20 that it does not state. Proposition 26,
  Theorem 27, Lemma 28, Theorem 31 and part 2 of Theorem 4 are written from it.
* **Proposition 12**, which is Theorem 5.3 of [LM22] rather than a result of the paper.
  It is stated once for each of the two models, and Theorems 3 and 31 take it as a
  hypothesis.

The results written from these have complete Lean proofs that depend on nothing else.
The library declares no axiom.
[`STATUS.md`](STATUS.md) gives the status of every statement, and is regenerated and
checked by CI.

A Lean proof here follows the paper's proof, and where the written argument does not
close the statement is left unproved and the reason recorded, rather than repaired by an
argument the authors have not seen.

## Where to read more

| | |
|---|---|
| [`SocialNetwork/MainResults.lean`](SocialNetwork/MainResults.lean) | the main theorems of the paper as Lean states them, in one place |
| [`SocialNetwork/Examples.lean`](SocialNetwork/Examples.lean) | the definitions on small cases, and the hypotheses of the main theorems shown to be satisfiable |
| [`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) | what formalising found in the paper: the statement that fails, the assumptions made, and the misprints and gaps |
| [`STATUS.md`](STATUS.md) | every statement of the paper and its status, generated from the blueprint and the sources |
| [`CONVENTIONS.md`](CONVENTIONS.md) | how the translation is written: the rules, the markers, the coordinates, the naming |
| [`GL24.md`](GL24.md) | the `M = 2` paper the proofs follow, read against the steps this paper shortens |

The blueprint at
<https://FelipePenafiel.github.io/social_network_lean/blueprint/> is the mathematical
contract between the paper and the repository: every statement of the paper with its Lean
name, and how each proof was formalised.

## Layout

```
SocialNetwork.lean            root module
SocialNetwork/Defs.lean       pressure matrices, π^{a,o}, trust, public opinion, S
SocialNetwork/Ladder.lean     ladder sets L^o, consensus sets C^o, steep ladders L̂^o
SocialNetwork/Trajectory.lean realisations (Aₙ, Oₙ)ₙ and the deterministic layer of §5
SocialNetwork/Consensus.lean  greedy dynamics from a consensus state reach a ladder
SocialNetwork/Favouring.lean  Definition 5, the first-repeat time τ(u), Appendix A pieces
SocialNetwork/Bias.lean       §3, via the variable-length memory (nₐ, cₚ) of eq. (6)
SocialNetwork/Frequencies.lean     i.i.d. uniform opinion words and the event E_ε^k of Prop 18
SocialNetwork/Skeleton.lean   Definition 3: jump rates, skeleton kernel, law of a realisation
SocialNetwork/Greedy.lean     Proposition 8 and Remark 4
SocialNetwork/Clocks.lean     the race between independent exponential clocks (Mathlib lacks it)
SocialNetwork/Kac.lean        Kac's lemma, in the half Proposition 9 uses and Mathlib lacks
SocialNetwork/Doeblin.lean    Doeblin's criterion, both halves, for any countable chain
SocialNetwork/Markov.lean     the law of a cylinder, and the Markov property of the skeleton
SocialNetwork/Minorisation.lean    the minorisation of the skeleton chain (the paper's p. 17)
SocialNetwork/Appendix.lean   Appendix A: Proposition 7, Lemmas 19 and 20, Remark 5, Prop 9
SocialNetwork/ContinuousTime.lean  eq. (3), the jump process, μ̃^β, Theorem 2.2
SocialNetwork/ConsensusExit.lean   Lemma 14: leaving a consensus set (Appendix B)
SocialNetwork/Metastability.lean   Corollary 15 and Theorem 3
SocialNetwork/ExitTime.lean   the mean exit time from a consensus set is positive and finite
SocialNetwork/JumpHold.lean   non-explosion for a jump-hold chain with a slow sub-family
SocialNetwork/NonExplosion.lean    the bound λ of equation (11) on the low-pressure pairs
SocialNetwork/Band.lean       the band of [GL24]'s Figure 2, for an arbitrary state space
SocialNetwork/BandCollapse.lean    the band is the process
SocialNetwork/Graphical.lean  the band of equation (3)'s model, and Theorem 1.1
SocialNetwork/Transfer.lean   equation (13), from the correspondence of p. 18 one way
SocialNetwork/Existence.lean  the correspondence the other way, and Theorem 1.2
SocialNetwork/Concentration.lean   Theorem 2.1, from equation (13) and Propositions 7–9
SocialNetwork/BiasedModel.lean     §3 assembled: S^α, C_α^o, L_α^o, Remarks 1, 2, 8
SocialNetwork/BiasedResults.lean   §3 and Appendix C: Theorem 4, Theorem 25 for the skeleton
SocialNetwork/BiasedNonExplosion.lean   Theorems 16 and 25.1, the biased twins of Theorem 1.1
SocialNetwork/BiasedTransfer.lean  equation (13) for the biased process
SocialNetwork/BiasedExistence.lean  Theorem 25.2, the invariant measure of the biased process
SocialNetwork/BiasedConcentration.lean  Proposition 26 and Theorem 27.1, after Proposition 9 and Theorem 2.1
SocialNetwork/BiasedConsensusExit.lean  Lemma 29, the biased twin of Lemma 14
SocialNetwork/BiasedHitting.lean   Lemma 28 and Theorem 27.2, the biased twins of Lemma 13 and Theorem 2.2
SocialNetwork/BiasedMetastability.lean  Corollary 30 and Theorem 31
SocialNetwork/BiasedExitTime.lean  the same for the biased process
SocialNetwork/MainResults.lean     the main theorems, restated in one place
SocialNetwork/Examples.lean   small cases, and the hypotheses of the main theorems met

blueprint/src/content.tex     the blueprint: every statement of the paper, with its Lean name
blueprint/src/packages/papergraph.py   the dependency graph of the paper's results
blueprint/blueprint.md        what Mathlib provides and what it does not, with line numbers
scripts/status.py             generates STATUS.md and the CI axiom check from the blueprint
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

The blueprint is a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
document, and builds independently of the Lean project:

```sh
pip install leanblueprint          # needs graphviz and its dev headers
leanblueprint pdf                  # blueprint/print/print.pdf
leanblueprint web                  # blueprint/web/index.html
leanblueprint serve                # to read the web version locally
```

Both the web version and the [pdf](https://FelipePenafiel.github.io/social_network_lean/blueprint.pdf)
are published from every push to `main`.

The web version draws two dependency graphs.  *Dependency graph* has one node per
result of the paper: the parts of a theorem, and the steps the blueprint splits a proof
into, are drawn as that theorem, and definitions, equations, remarks and the
formalisation's own lemmas are drawn through.  *Full dependency graph* has every node of
the blueprint.

## Contributing

Read [`CONVENTIONS.md`](CONVENTIONS.md) first, and the blueprint after it: between them
they are the contract between the paper and this repository. In short — cite the paper's
statement, keep the definitions readable against it, follow the paper's proof, and update
the blueprint in the same commit.

Before pushing:

```sh
python3 scripts/status.py          # rewrites STATUS.md; CI fails if it is not current
lake build
```

## Licence

Apache 2.0, which covers the code and the documentation; see [`LICENSE`](LICENSE).

The two papers are included for reference and are not covered by it.
[`2607.19651v1.pdf`](2607.19651v1.pdf) (F. Penafiel and K. Laxa,
[arXiv:2607.19651v1](https://arxiv.org/abs/2607.19651v1)) and [`GL24.pdf`](GL24.pdf)
(A. Galves and K. Laxa, [arXiv:2202.12871v4](https://arxiv.org/abs/2202.12871v4)) are
distributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), the licence of
their arXiv deposits.
