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

Every numbered statement of the paper — 58 statements and displayed equations — is
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
* **Theorem 1.1 and its biased twin Theorem 16** — the process does not explode.  The
  paper asserts the sandwich (11) rather than constructing it; [GL24] pp. 12–14 does
  construct it, and that construction is formalised (`SocialNetwork/Band.lean` and
  `SocialNetwork/BandCollapse.lean`), down to the identification of the constructed
  process with the one equation (3) defines.  It is written for an arbitrary state space,
  so both models instantiate it, which is what Appendix C prescribes;
* **Equation (13) and Theorem 1.2** — `μ^β` exists, is unique, and is `μ̃^β / q_β`
  normalised.  The equivalence the paper cites at p. 18 between invariance for the
  process and for the skeleton is proved in both directions
  (`SocialNetwork/Transfer.lean`, `SocialNetwork/Existence.lean`), and neither needs a
  forward equation for the semigroup;
* **Lemma 14**, both parts, and Corollary 15 with it — the two-sided control of the exit
  from a consensus set that Appendix B proves by comparing exponential clocks.  Appendix
  B's composition of its estimates does not hold together as written, and the same
  estimates are composed here by a first-step induction, with the paper's constant;
* the biased model of Section 3, with Propositions 21, 17, 22 and 24, and **Proposition 18
  and part 1 of Theorem 4** — the negative-bias half of the phase transition: almost
  surely all but one actor eventually stop expressing;
* **Theorem 25**, the invariant measure of the biased skeleton, by Appendix C's route,
  and **Lemma 29** with Corollary 30, the biased twins of Lemma 14 and Corollary 15.

**Written out modulo one citation**, Theorem 5.3 of [LM22], which the paper invokes as
Proposition 12 and nothing in this library can discharge: **both metastability theorems,
3 and 31**, which also rest on Lemmas 13 and 28 respectively. It is declared as an `axiom` rather than left as a `sorry`, so that it does
not sit in the inventory of outstanding work pretending to be pickable. There have to be
two, one per process; [`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) §3 says why a single
abstract axiom would be inconsistent.

**Written out and resting on an obstruction.** Proposition 7 is assembled from its three
stages and waits on Lemmas 19 and 20, the two written proofs of Appendix A that do not
compose; Proposition 9 and Theorem 2.1 wait behind it. Each inherits `sorryAx` from its
obstruction and from nothing else, so it turns green the moment that one does.

What is unproved is unproved for two reasons, which [`STATUS.md`](STATUS.md) keeps
apart because they are not comparable: the paper's own proof does not compose, or the
statement is a citation from outside the paper.  Nothing waits on Mathlib any more.

**Lean checks the paper's arguments, not only its statements.** A Lean proof here follows
the paper's proof; where the written argument does not close, the statement is left
unproved and the obstruction is written down, rather than repaired by an argument the
authors have not seen. That holds even when another argument would close the statement —
Lemmas 19 and 20 are the cases to look at. The rule is stated in full in
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
SocialNetwork/ContinuousTime.lean  eq. (3), the jump process, μ̃^β, Theorem 2.2
SocialNetwork/ConsensusExit.lean   Lemma 14: leaving a consensus set (Appendix B)
SocialNetwork/Metastability.lean   Corollary 15 and Theorem 3
SocialNetwork/JumpHold.lean   non-explosion for a jump-hold chain with a slow sub-family
SocialNetwork/NonExplosion.lean    the bound λ of equation (11) on the low-pressure pairs
SocialNetwork/Band.lean       the band of [GL24]'s Figure 2, for an arbitrary state space
SocialNetwork/BandCollapse.lean    the band is the process
SocialNetwork/Graphical.lean  the band of equation (3)'s model, and Theorem 1.1
SocialNetwork/Transfer.lean   equation (13), from the correspondence of p. 18 one way
SocialNetwork/Existence.lean  the correspondence the other way, and Theorem 1.2
SocialNetwork/Concentration.lean   Theorem 2.1, from equation (13) and Propositions 7–9
SocialNetwork/BiasedModel.lean     §3 assembled: S^α, C_α^o, L_α^o, Remarks 1, 2, 8
SocialNetwork/BiasedResults.lean   §3 and Appendix C: Theorems 4, 25, 27.1
SocialNetwork/BiasedNonExplosion.lean   Theorem 16, the biased twin of Theorem 1.1
SocialNetwork/BiasedConsensusExit.lean  Lemma 29, the biased twin of Lemma 14
SocialNetwork/BiasedHitting.lean   Lemma 28 and Theorem 27.2, the biased twins of Lemma 13 and Theorem 2.2
SocialNetwork/BiasedMetastability.lean  Corollary 30 and Theorem 31

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

Apache 2.0.
