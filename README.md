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

## Four questions, four files

| | |
|---|---|
| **Which proofs of the paper resist formalisation?** | [`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) — every obstruction, sorted by what it asks of the authors, with the mathematics in the blueprint |
| **How far has the formalisation got?** | [`STATUS.md`](STATUS.md) — every statement of the paper and its status, generated from the blueprint and the sources, checked by CI |
| **How is the translation written?** | [`CONVENTIONS.md`](CONVENTIONS.md) — the three rules, the markers, the coordinates, the naming |
| **Where are the steps the paper shortens?** | [`GL24.md`](GL24.md) — the `M = 2` paper the proofs follow, read against every obstruction |

The blueprint at
<https://FelipePenafiel.github.io/social_network_lean/blueprint/> is the mathematical
contract between the paper and the repository, and holds the detail behind all four.

## Where things stand

Every numbered statement of the paper — 56 statements and displayed equations — is
stated in Lean, and [`STATUS.md`](STATUS.md) says of each one whether it is proved.

**Proved outright**, depending on nothing but Lean's own axioms:

* the deterministic layer — the state space, the expression operator and its
  conservation law, the ladder and consensus geometry of Definitions 1, 2 and 4, and
  the vocabulary of Appendix A;
* the discrete-time probabilistic layer — the jump rates of equation (3), the skeleton
  kernel of Definition 3, the law of a realisation via Mathlib's Ionescu–Tulcea
  theorem, Propositions 5, 6 and 8 with Remarks 4 and 5;
* **Doeblin's criterion**, both halves, for an arbitrary Markov kernel on a countable
  space (`SocialNetwork/Doeblin.lean`), and with it **Theorem 1.2 for the skeleton**:
  `μ̃^β` exists and is unique;
* **Kac's inequality**, which is the half of Kac's lemma Proposition 9 uses;
* the biased model of Section 3, with Propositions 21, 17 and 24, and **Proposition 18
  and part 1 of Theorem 4** — the negative-bias half of the phase transition: almost
  surely all but one actor eventually stop expressing.

**Proved modulo one citation**, Theorem 5.3 of [LM22], which the paper invokes as
Proposition 12 and nothing in this library can discharge: **both metastability theorems,
3 and 31**. It is declared as an `axiom` rather than left as a `sorry`, so that it does
not sit in the inventory of outstanding work pretending to be pickable. There have to be
two, one per process; [`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) §3 says why a single
abstract axiom would be inconsistent.

**Written out and resting on an obstruction.** Proposition 7 is assembled from its three
stages and waits on Lemmas 19 and 20, the two written proofs of Appendix A that do not
compose; Proposition 9 and Theorem 2.1 wait behind it. Theorem 25 is written on Appendix
C's own route and rests on Proposition 22. Each inherits `sorryAx` from its obstruction
and from nothing else, so it turns green the moment that one does.

What is unproved is unproved for three reasons, which [`STATUS.md`](STATUS.md) keeps
apart because they are not comparable: Mathlib has no theory of the object, the paper's
own proof does not compose, or the statement is a citation from outside the paper.

**Lean checks the paper's arguments, not only its statements.** A Lean proof here follows
the paper's proof; where the written argument does not close, the statement is left
unproved and the obstruction is written down, rather than repaired by an argument the
authors have not seen. That holds even when another argument would close the statement —
Theorem 25 is the case to look at. The rule is stated in full in
[`CONVENTIONS.md`](CONVENTIONS.md), and [`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) is
what it reports to.

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
SocialNetwork/ContinuousTime.lean  eq. (3), the jump process, Theorems 1, 2, 3
SocialNetwork/BiasedModel.lean     §3 assembled: S^α, C_α^o, L_α^o, Remarks 1, 2, 8
SocialNetwork/BiasedResults.lean   §3 and Appendix C: Theorems 4, 16, 25, 27, 31

blueprint/src/content.tex     the blueprint: every statement of the paper, with its Lean name
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

Apache 2.0.
