# Conventions for the translation into Lean

Everything in this repository is a translation of arXiv:2607.19651. These are the
rules the translation follows, so that a reader who knows the paper can read the Lean,
and so that a green node means what it looks like it means.

[`STATUS.md`](STATUS.md) is how far the translation has got.
[`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) is what it has not been able to close.
This file is how it is written.

---

## 1. The three rules

**1. Every declaration that corresponds to a numbered statement cites it, and the
blueprint is updated in the same commit.** The docstring names the statement
(`Proposition 5`, `eq. (6)`, …); `blueprint/src/content.tex` carries the `\lean` list
of the node, and `\leanok` on the proof once the proof is there. `python3
scripts/status.py --check` verifies that every name cited exists and that no `sorry`
is missing from the blueprint.

**2. A definition must be readable against the paper.** Where a reformulation is used
for convenience — the scaled coordinates of §2, or `(M - 1) * u a p = - u a o` standing
for `u (·, p) = - u (·, o) / (M - 1)` — the docstring says so.

**3. A proof must follow the paper's proof.** Where the paper argues a statement, the
Lean proof reproduces *that* argument, not a different route to the same conclusion.
The point of formalising is to check the reasoning; a proof that arrives some other way
checks nothing about what the paper wrote, and leaves a green node claiming more than
it has earned.

The exception is **what the paper leaves implicit**: a step asserted with "note that"
or "by definition", measurability, the plumbing of the sample space. Supply it — there
is nothing else to do — and mark it, so a reader can see which part of a green node the
paper actually wrote.

**Departing from a proof the paper does give needs a written reason, and the reason has
to be that the paper's route cannot be followed** — Mathlib lacks the theory, or the
written proof does not compose. Convenience is not a reason: a shorter route that
bypasses the paper's argument is a check not performed. A departure of the second kind
is a finding about the paper and belongs in `FOR-THE-AUTHORS.md`, next to Lemmas 19
and 20.

There is exactly one such departure in the repository at present, Proposition 7, and it
is written out at the declaration and in `FOR-THE-AUTHORS.md` §1.4.

## 2. Markers

Every formalised proof opens by saying which of three things it is, in the docstring
and in the blueprint's `\begin{proof}`, in one of these forms:

- `Follows the paper's proof of Proposition 5.`
- `Supplies a step the paper asserts: … .`
- `No counterpart in the paper: … .`

The blueprint's *What the formalised proofs check* section audits every formalised
proof on exactly that question, and keeps a running count of the three.

## 3. Scaled coordinates

The paper's matrices have entries in `ℤ + (1/(M-1))ℤ`. Everything here is stated for
the rescaled matrix

```
v (a, o) := (M - 1) * u (a, o)
```

which is an *integer* matrix. Under this rescaling the operator of equation (1) adds
`M - 1` on the expressed column and subtracts `1` on the others. The rescaling is a
bijection, so no statement changes, and the arithmetic of the paper becomes plain
integer arithmetic — in particular the estimate behind Proposition 8, that two distinct
entries differ by at least `1/(M-1)`, becomes the statement that two distinct integers
differ by at least `1`.

A Lean statement therefore reads `v` where the paper reads `u`. The blueprint keeps the
paper's coordinates; the discrepancy is exactly this rescaling, and nothing else.

## 4. Naming

| The paper | Lean |
|---|---|
| an actor `a ∈ A`, an opinion `o ∈ O` | `Actor N`, `Opinion M` — both `Fin` |
| a matrix of social pressures | `Pressure N M := Actor N → Opinion M → ℤ` |
| `π^{a,o}` | `express a o` |
| a property `u ∈ X` | a predicate `IsX`, a `structure` when it has several fields |
| the set `X` | `xSet`, defined as `{u | IsX u}` |
| a realisation `(Aₙ, Oₙ)ₙ` | `Trajectory N M`, with `.actor` and `.opinion` |
| the matrix after `n` expressions | `T.state u n` |
| the greedy event `ξₙ^u` | `IsGreedyAt T u n`, and `greedyEvents` for the set |
| `τ (u)` | `firstRepeat T`, which is `τ (u) - 1` — see its docstring |
| everything of Section 3 | the `SocialNetwork.Bias` namespace, and a `biased` prefix |

The biased model shadows the unbiased one throughout: `IsBiasedState`,
`biasedLadderSet`, `biasedZeta`, `biasedMetastability`. Where a biased result is proved
by transporting an unbiased one, the docstring says which, and the Lean proof is the
unbiased proof transposed rather than a new argument.

Hypotheses are named for what they are (`hM : 2 ≤ M`, `hβ : 0 ≤ β`, `hu : IsState u`),
and the standing hypotheses of the paper — `N ≥ 3`, `M ≥ 2` — are arguments rather than
`variable`s, so that a statement can be read without its context.

## 5. `sorry` and `axiom`

The library is **not** `sorry`-free, by design: it states every numbered result of the
paper, and the ones whose proofs are not formalised carry a `sorry`. What is not
allowed is a `sorry` leaking into a result claimed complete, and CI enforces that.

A `sorry` says *this is work someone could do*. Where that is false — the statement is
cited from outside the paper and nothing in this library could ever discharge it — the
declaration is an `axiom` instead, so that it does not sit in the inventory of
outstanding work pretending to be pickable. There are two, both Theorem 5.3 of [LM22];
`FOR-THE-AUTHORS.md` §3 says why there have to be two.

CI gates both: no declaration claimed complete may reach `sorryAx` or either axiom.

## 6. A proof may precede its ancestors

A result whose own proof is written but whose upstream lemmas are still `sorry`
compiles, inherits `sorryAx` from them, and turns green the moment they do — with no
edit. Writing the downstream proof first is deliberate, and it is the only test of
whether the upstream *statements* are strong enough: Theorem 3 was proved this way, and
doing so is what exposed that the previous statement of Proposition 12 could never be
instantiated.

`STATUS.md` keeps the two apart, as **proved** and **proof written, rests on …**.

## 7. The blueprint is the contract

`blueprint/src/content.tex` states every numbered result of the paper, records the Lean
name of each, and draws the dependency graph. A change to the code updates it in the
same commit. It is also the input to the tooling:

```sh
python3 scripts/status.py          # rewrite STATUS.md
python3 scripts/status.py --check  # what CI runs; no Lean toolchain needed
python3 blueprint/check_decls.py   # the same name check against plasTeX's own list
```

`scripts/status.py` refuses a `sorry` that no blueprint node accounts for, a Lean name
the blueprint cites that the library does not declare, and an unproved statement with
no recorded reason. The CI axiom check is generated from the same source, so a
`\leanok` that has not been earned fails the build rather than going unnoticed.

`blueprint/blueprint.md` is the engineering companion and carries no statement tables —
only the audit of what Mathlib does and does not provide, with exact names, files and
line numbers, checked against the pinned revision.
