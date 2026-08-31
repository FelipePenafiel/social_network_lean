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
**Proposition 8** with Remark 4, and **Remark 5** — the bound `η` and its iterate `η^m`.

The **continuous-time process** is built — the jump-hold representation is a discrete-time
chain carrying one real coordinate, so `Kernel.traj` constructs it — and with it the jump
times, the process `U_t`, the transition semigroup and the hitting times `R^{β,u}(θ)`.

The **biased model of Section 3** is assembled: memory profiles, the operator `π_α^{a,o}`, the
state space `S^α`, the generator `G̃` of equation (7), the sets of equations (8) and (9), and
the biased skeleton and process.  **Propositions 21, 17 and 24 are proved**, by the transports
Appendix C and Section 5.4 assert — of Propositions 5, 6 and 8 respectively, and **Corollary 30**
is Corollary 15 transposed.  Proposition 22 is the one transport that does not work; see
[`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md).

**Every numbered statement of the paper is now stated in Lean.**  The ones whose proofs are not
formalised carry a `sorry` and are marked 🟡 in the blueprint.  They are unproved for four
distinct reasons, which the blueprint keeps apart: blocked on missing Mathlib theory (Doeblin's
criterion, Kac's lemma, Poisson point processes), blocked on the paper (Lemmas 19 and 20, whose
written proofs do not compose — repairs are recorded), not a result of this paper at all
(Proposition 12; see below), or simply routine and not yet done.

**Lemma 13** is proved, and writing it turned up a third kind of obstruction.  Its proof uses
two inequalities the paper *displays inside proofs* but never states — a quantitative bound
whose limit is Theorem 2.2, and equation (19), which reads Corollary 11 quantitatively — and
both Theorem 2.2 and Corollary 11 are stated only as limits.  A limit has thrown the rate away,
so Lemma 13 does not follow from the numbered statements it cites.  The two displays are now
Lean statements of their own, each carrying a `sorry`, and Lemma 13 rests on them rather than
on an argument nobody has seen.

A proof does **not** have to wait for its ancestors.  A result whose own proof is written but
whose upstream lemmas are still `sorry` compiles fine, inherits `sorryAx` from them, and turns
green the moment they do — with no edit.  Writing the downstream proof first is also the only
test of whether the upstream *statements* are strong enough: **Theorem 3** is proved this way,
and doing so is what exposed that the previous statement of Proposition 12 could never be
instantiated.

The routine list is now empty.  `sum_ge_of_injective` (that `N` distinct naturals sum to at
least `0 + 1 + ⋯ + (N-1)` — a Mathlib gap in its own right), the two measurability lemmas for
the biased greedy events, `measurable_process`, **Remark 8** and **Remark 5 entire** are
proved.  Remark 5 was the last item on that list that was mathematics rather than bookkeeping.
Its bound `η` needs the comparison showing that the worst case over `L̂` is attained on `L`,
which the paper writes down and does not argue, and that comparison rests on the monotone form
of the same Mathlib gap — that `N-1` distinct naturals `≥ 1` dominate `1, 2, …, N-1` term by
term under any increasing function.  Its iterate `η^m`, which the sketch of Proposition 9 uses
without deriving, reruns Proposition 8's induction along the Ionescu–Tulcea kernels; unlike
`ζ_β`, `η` is not uniform in the matrix, so the finite-horizon step has to carry the steepness
of the state the history reaches.

What is left over from that list is `measurable_hittingTimeCts`, which turned out not to be
routine at all: the hitting time is an infimum over an uncountable family of times, and so
needs path regularity that holds only almost surely.  The blueprint says why, and what has to
be decided before it can be done.

### The one axiom

`SocialNetwork.exitTime_approx_exponential` — **Proposition 12** — is an `axiom`, not a
`sorry`.  It is not a result of arXiv:2607.19651: the paper derives it from Theorem 5.3 of
[LM22], a metastability estimate for a general time-homogeneous strong Markov process, and
nothing inside this library can discharge it.  Declaring it says so plainly, and keeps it from
sitting in the inventory of `sorry`s as if it were work someone could pick up.

It is attached to *this* process on purpose.  Stated abstractly, over an arbitrary family of
measures and an arbitrary hitting time, it would be **inconsistent**: the zero measure with an
empty ladder set satisfies (15)–(18) vacuously and falsifies the conclusion at `t = 0`.  What
rules that out is the strong Markov property, which is exactly the content of [LM22].  Theorem
31 will therefore need its own twin for the biased process.

**Theorem 3** is now proved from it, together with the four assumptions (15)–(18) checked for
this model as Section 5.3 does.

The library is **not** `sorry`-free, by design.  What CI enforces is that no declaration listed
as complete in `.github/workflows/ci.yml` depends on `sorryAx` — **or on the [LM22] axiom**.  A
separate step records which results are complete modulo that one citation, so the trust surface
stays visible.  Every run also prints an inventory of the outstanding `sorry`s.

Formalising surfaced places where the paper needs correcting, none of which affects its
results.  Two are in Appendix A (Lemmas 19 and 20); one is that the second condition of
equation (6) is not stable under `π_α^{a,o}`, though the justification the paper gives for it
proves a stronger condition that is; and one is that Corollary 15 — like every statement of the
form "for any `l ∈ L^o`" — is vacuous unless `L^o` is inhabited, which the paper never records.
`ladderOf` is the witness.  All are stated precisely in the blueprint, as are the three steps
of Section 5.3 that are asserted rather than argued: the inclusion `L ⊆ L^o ∪ C^{-o}`, the
supremum `sup β e^{-β/a} = a e^{-1}`, and the threshold above which `ε₁ + ε₂ ≤ 1/2`.

[`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) collects, in one place, everything formalising has
not been able to close: the three written proofs that do not compose (Lemmas 19 and 20, and
Proposition 22), the statements that had to be changed to be usable, the one axiom and the
second one Theorem 31 will need, and the steps the text asserts that had to be supplied.  It
also records the rule this repository works under: **no proof of a statement of the paper has
been invented here.**  Where the written argument does not close, the statement is left
unproved and the obstruction is written down, rather than repaired by an argument the authors
have not seen.

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
blueprint/src/content.tex     the blueprint: every statement of the paper, with its Lean name
blueprint/blueprint.md        what Mathlib provides and what it does not, with names and line numbers
```

## Blueprint

The blueprint is a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
document: it states every numbered result of the paper, records the Lean name of
each, and draws the dependency graph, in which a green node is formalised and a
blue one is stated with a `sorry`.

```sh
pip install leanblueprint          # needs graphviz and its dev headers
leanblueprint pdf                  # blueprint/print/print.pdf
leanblueprint web                  # blueprint/web/index.html
leanblueprint serve                # to read the web version locally
python3 blueprint/check_decls.py   # every Lean name cited must exist
```

`blueprint/src/content.tex` is the source, and it is the contract between the
paper and this repository: a change to the code updates it in the same commit.
`blueprint/blueprint.md` is its engineering companion and carries no statement
tables — only the audit of what Mathlib does and does not provide, with exact
names, files and line numbers, together with the commands to re-check it.

The blueprint is published at
<https://FelipePenafiel.github.io/social_network_lean/blueprint/> and the pdf at
<https://FelipePenafiel.github.io/social_network_lean/blueprint.pdf>, from every
push to `main`.

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

Three rules:

1. Every new declaration that corresponds to a numbered statement of the paper cites it in
   its docstring (`Proposition 5`, `eq. (6)`, …), and `blueprint/src/content.tex` is updated
   in the same commit — the `\lean` list of the statement, and `\leanok` on the proof once
   the proof is there. `python3 blueprint/check_decls.py` checks that every name cited
   exists.
2. A definition must be readable against the paper. Where a reformulation is used for
   convenience — as with the scaled coordinates, or with `(M - 1) * u a p = - u a o`
   standing for `u (·, p) = - u (·, o) / (M - 1)` — say so in the docstring.
3. A *proof* must **follow the paper's proof**. Where the paper argues a statement, the Lean
   proof reproduces that argument — not a different route to the same conclusion. The point
   of formalising is to check the reasoning; a proof that reaches the conclusion some other
   way checks nothing about what the paper wrote, and leaves a green node claiming more than
   it has earned.

   The exception is **what the paper leaves implicit**: a step asserted with "note that" or
   "by definition", measurability, the plumbing of the sample space. Supply what is needed —
   there is nothing else to do — and mark it, so a reader can see which part of a green node
   the paper actually wrote. Mark it in the docstring and in the blueprint's `\begin{proof}`,
   in the form used by the proofs already there:

   - `Follows the paper's proof of Proposition 5.`
   - `Supplies a step the paper asserts: … .`
   - `No counterpart in the paper: … .`

   **Departing from a proof the paper does give needs a written reason, and the reason has
   to be that the paper's route cannot be followed** — Mathlib lacks the theory, or the
   written proof does not compose. Convenience is not a reason: a shorter route that
   bypasses the paper's argument is a check not performed. A departure of the second kind
   is a finding about the paper and belongs in "Three corrections to the paper", next to
   Lemmas 19 and 20.

   `blueprint/src/content.tex` carries an audit of every proof currently formalised against
   the paper, under "What the formalised proofs check". Keep it current.


## Licence

Apache 2.0.
