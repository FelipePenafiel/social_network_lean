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

## Three questions, three files

| | |
|---|---|
| **Which proofs of the paper resist formalisation?** | [`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) — every obstruction, sorted by what it asks of the authors, with the mathematics in the blueprint |
| **How far has the formalisation got?** | [`STATUS.md`](STATUS.md) — every statement of the paper and its status, generated from the blueprint and the sources, checked by CI |
| **How is the translation written?** | [`CONVENTIONS.md`](CONVENTIONS.md) — the three rules, the markers, the coordinates, the naming |

The blueprint at
<https://FelipePenafiel.github.io/social_network_lean/blueprint/> is the mathematical
contract between the paper and the repository, and holds the detail behind all three.

## Where things stand

The **deterministic layer** is proved: the state space, the expression operator and the
conservation law behind it, the ladder/consensus geometry of Definitions 1, 2 and 4,
Propositions 5 and 6, and the vocabulary of Appendix A. Proposition 7 is assembled from
its three stages and waits only on Lemmas 19 and 20 — the two written proofs of
Appendix A that do not compose.

The **discrete-time probabilistic layer** is built and proved: the jump rates of equation
(3), the skeleton kernel of Definition 3 as a `Kernel (Pressure N M) (Pressure N M)`, the
law of a realisation via Mathlib's Ionescu–Tulcea theorem, the greedy events `ξₙ^u` as
measurable sets, Proposition 8 with Remark 4, and Remark 5 entire.

The **continuous-time process** is built — the jump-hold representation is a discrete-time
chain carrying one real coordinate, so `Kernel.traj` constructs it — and with it the jump
times, the process `U_t`, the transition semigroup and the hitting times `R^{β,u}(θ)`.

The **biased model of Section 3** is assembled: memory profiles, the operator `π_α^{a,o}`,
the state space `S^α`, the generator `G̃` of equation (7), the sets of equations (8) and
(9), and the biased skeleton and process. Propositions 21, 17 and 24 are proved by the
transports Appendix C and Section 5.4 assert, and Corollary 30 is Corollary 15 transposed.

**Both metastability theorems — 3 and 31 — are proved**, modulo one citation used twice:
Theorem 5.3 of [LM22], which the paper invokes as Proposition 12 and which nothing inside
this library can discharge. It is declared as an `axiom` rather than left as a `sorry`, so
that it does not sit in the inventory of outstanding work pretending to be pickable. There
have to be two, one per process; [`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) §3 says why a
single abstract axiom would be inconsistent.

Every numbered statement of the paper is stated in Lean, with one exception recorded in
[`STATUS.md`](STATUS.md). What is unproved is unproved for five distinct reasons, which
that file keeps apart because they are not comparable: one group will never close here,
one needs mathematics only the authors can supply, and one is only work.

**No proof of a statement of the paper has been invented here.** Where the written
argument does not close, the statement is left unproved and the obstruction is written
down, rather than repaired by an argument the authors have not seen. That rule is what
`FOR-THE-AUTHORS.md` exists to report on, and
[`CONVENTIONS.md`](CONVENTIONS.md) states it in full.

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
