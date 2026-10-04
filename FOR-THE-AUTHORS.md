# Where the paper resists formalisation

For Felipe Penafiel and Kádmo Laxa.  This file collects everything in
arXiv:2607.19651 that formalising has *not* been able to close, and separates the
places that need a decision from the places that only need work.

**The rule this repository follows, and why this file exists.**  A Lean proof here
must follow the paper's proof; a departure needs a written reason, and the reason
must be that the paper's route cannot be followed.  **No proof of a statement of
the paper has been invented here.**  Where the written argument does not close, the
statement is left carrying a `sorry` and the obstruction is recorded — in the
blueprint for the mathematics, and here for the decision.  Nothing in §1 has been
"repaired" by an argument you have not seen.

Three files, three jobs.  [`STATUS.md`](STATUS.md) is the generated index: every
statement of the paper, whether it is proved, and — for the ones that are not — which
of three kinds of obstruction it has met.  It is rebuilt from the sources and checked by
CI, so it cannot drift.  The blueprint (`blueprint/src/content.tex`, chapter *Notes on
the formalisation*) holds the mathematics of each item.  **This file says what each one
asks of you**, and nothing else.

[`GL24.md`](GL24.md) reads the `M = 2` paper your proofs follow against this list:
which of the shortened steps are written out there, which are not, and which of
the requests below [GL24] has already answered.

---

## At a glance

**These need a decision.**  Nothing in the repository can move until you make it.

| | Statement | The problem | What we need from you |
|---|---|---|---|
| [§1.1](#1-proofs-that-do-not-survive-formalisation) | **Lemma 19** | the `⌊m⌋ + 1` distinct actors are asserted, never constructed, and the degenerate case is ruled out through the wrong hypothesis | the construction, and the corrected case split.  A proposal is in the blueprint, for you to check or reject |
| [§1.2](#1-proofs-that-do-not-survive-formalisation) | **Lemma 20** | the induction invariant is not preserved: the expressing actor's row is reset, and at the last step the bound is negative | an invariant that survives.  A proposal is in the blueprint |
| [§2.7](#2-statements-that-had-to-be-changed) | **Lemma 13** | rests on two inequalities displayed inside proofs and never stated; the numbered statements they are attributed to are limits, which have thrown the rate away | whether either display should become a numbered statement.  Only that: both are steps of your own proofs, [GL24] writes both out, and both are now proved here |

**These are recorded, and need nothing.**  Formalising turned each one up; the
repository has already taken the only route available, and says so at the declaration.

| | Statement | What was found |
|---|---|---|
| [§1.3](#1-proofs-that-do-not-survive-formalisation) | **Proposition 22** | **Withdrawn.**  This file reported that it does not follow from Proposition 6; that came from reading your slack `½γ` as `1/(2γ)`.  With `½γ` it follows exactly as you say, and it is **proved** — and **Theorem 25** with it, by your route |
| [§1.7](#1-proofs-that-do-not-survive-formalisation) | **Lemma 14** | Appendix B multiplies a bound on `τ₁⁻ᵒ` by one on `τ₂⁻ᵒ` conditioned on `τ₁⁻ᵒ ≥ t`, through a conditioning on an event that involves the interval being bounded.  Your rates compose without it, by a first-step induction, with your constant.  **Proved**, and **Lemma 29** with it, as Appendix C says |
| [§1.4](#1-proofs-that-do-not-survive-formalisation) | **Proposition 7** | the written route carries `⋃_o S^o` from `τ(u)` to `N+1`, which needs a stability the paper never proves.  Applying Lemma 20 where Lemma 19 lands removes the need, with your arithmetic unchanged.  **Written out**, resting on Lemmas 19 and 20 |
| [§1.6](#1-proofs-that-do-not-survive-formalisation) | **Proposition 9** | "without visiting `u`" does not come from Proposition 7.  It is Corollary 8 of [GL24], and the argument is written out and machine-checked here.  **Written out**, resting on Lemmas 19 and 20 |
| [§2.12](#2-statements-that-had-to-be-changed) | **Theorem 2.1** | written out along your pp. 20–21, from equation (13), Propositions 7, 8 and 9 and Corollary 10, and **resting on Lemmas 19 and 20** through them.  One bound in it, `ζ_β^{(M+1)N} ≥ (MN)^{-(M+1)N}`, fails at `β = 0`; `(1+MN)^{-(M+1)N}` is used instead, and only `C` changes |
| [§1.5](#1-proofs-that-do-not-survive-formalisation) | **Lemma 28** | the biased twin of Lemma 13, so it inherits Lemma 13's two missing displays in biased form |
| [§2.1](#2-statements-that-had-to-be-changed) | **Proposition 12** | with `ε₁ ε₂ s₁ s₂` bound ahead of `β`, the hypotheses are unsatisfiable and Theorem 3 could never have followed.  Made functions of `β` |
| [§2.2](#2-statements-that-had-to-be-changed) | **Corollaries 15 and 30** | vacuous unless `L^o ≠ ∅`, which is nowhere recorded.  Witnesses supplied; both now proved |
| [§2.3](#2-statements-that-had-to-be-changed) | **Equation (6)** | the second condition is not stable under `π_α^{a,o}`, though your justification for it proves a stronger one that is |
| [§2.4](#2-statements-that-had-to-be-changed) | **Definition 4** | needs a sign condition to be the set the proofs use |
| [§2.6](#2-statements-that-had-to-be-changed), [§3.3](#3-the-two-axioms) | **Theorem 31** | its route needs a biased Proposition 12, which the paper does not state.  Declared as a second axiom; Theorem 31 is written out from it, and rests on Lemma 28 besides |
| [§2.8](#2-statements-that-had-to-be-changed) | **Proof of Lemma 13** | `τ` is exponential of mean `1/(MN)`, so `P(τ > β) = e^{-MNβ}`; the proof writes `e^{-β/(MN)}`.  Harmless — the written form is the weaker one |
| [§3](#3-the-two-axioms) | **Proposition 12, twice** | it is Theorem 5.3 of [LM22], not a result of this paper, and cannot be stated once for both models without becoming inconsistent |
| [§5](#5-not-the-papers-fault) | **Remark 6** | its horizon is `N`, not `(M+1)N`: part 2 of Theorem 2 concludes `L`, not `L^o`, and cannot be quoted as it stands.  **Proved** outright, its route needing only the last stage of Proposition 7 |
| [§2.10](#2-statements-that-had-to-be-changed) | **Proposition 9** | the statement quantifies over `u ∉ L̂` with no other hypothesis, but its proof calls Proposition 7, which is stated on `S` | `IsState u` added.  The paper works in `S` throughout |
| [§5](#5-not-the-papers-fault) | **Proposition 17** | its proof needs no hypothesis on `α`, only `γ > 0`; the `α < 0` in the statement is where Section 5.4 uses it.  Stated in Lean as you state it |
| [§2.5](#2-statements-that-had-to-be-changed) | **Equation (13)** | as stated it takes both `μ` and `μ̃` as given, so it yields the *uniqueness* half of Theorem 1.2 and presupposes existence.  Existence is the converse of the equivalence it cites, which is what the paper uses.  **Both directions are proved** here, and Theorem 1.2 with them; restating (13) as the converse would make the statement say what is used, and nothing waits on it |
| [§5](#5-not-the-papers-fault) | **Theorem 1.2, for the skeleton** | **Proved**, both halves, from the criterion and your page-17 minorisation.  The existence half needs no Markov-chain theory — on a countable space the excursion measure is a sum, not a limit.  Your `ε*` becomes an explicit constant, (12) is proved from *any* matrix, which is what lets the minorising measure be a single Dirac mass, and the Lean statement drops your `N ≥ 3`.  Theorem 1.2 in continuous time is now **proved** as well: equation (13) gives its uniqueness half, and the converse of the equivalence (13) cites gives existence |
| [§5](#5-not-the-papers-fault) | **Kac's lemma in Proposition 9** | the proof opens with the *identity*, which needs irreducibility, and then uses only the *inequality*, which holds for every invariant probability measure.  Nothing there waits on Theorem 1.2; the inequality is **proved** outright here |
| [§2.11](#2-statements-that-had-to-be-changed), [§5](#5-not-the-papers-fault) | **Corollary 11** | the sentence "`τ` … independent from `(U_t^{β,u})_t`" admits a reading under which the corollary is **false**.  Under the reading your equation (19) uses — `τ` the process's own first jump time from `0` — it is true and **proved** here |
| [§5](#5-not-the-papers-fault) | **Theorem 4, part 1** | the "strong Markov property at `T_N`" is the *simple* one: for the skeleton `T_N` is a deterministic index.  Mathlib has no strong Markov property, and none was needed.  **Proved** |

---

## 1. Proofs that do not survive formalisation

Two written proofs do not compose — §§1.1–1.2.  Each is left unproved on
purpose.  A repair is new mathematics and is yours to write, not the
formalisation's to guess.  A third, Proposition 22 (§1.3), stood here because of
this repository's own misreading, and is withdrawn.

Four more belong here for different reasons.  **Proposition 7** (§1.4) composes
only along a different route; the missing step turned out to be avoidable, so it
is proved, but you should know the written route does not run.  **Lemma 14**
(§1.7) is of the same kind: its estimates are right and their written
composition is not, so it is proved along another, with your constant.  **Lemma 28**
(§1.5) is blocked one level up, on ingredients Lemma 13 needs that the paper
displays inside proofs rather than states.  And **Proposition 9** (§1.6) stood
here as an item needing a decision, for one clause of one sentence; it does
not any more, because [GL24] states that clause as its Corollary 8.

### 1.1 Lemma 19 — the `⌊m⌋ + 1` distinct actors

*Blueprint:* `note-lem19`. *Lean:* `SocialNetwork.isFavouring_state_firstRepeat`.

The written proof asserts, "by (25)", a sequence of `⌊m⌋ + 1` distinct actors
without giving the construction, and rules out the degenerate case `m = 0` through
`τ (u) = 2` rather than through `m = 0` itself.

**What is needed:** the construction, and the corrected case split.  The blueprint
records a first-passage decomposition of the backward walk that does produce the
actors, and the case split that works — but as a *proposal for you to check*, not
as something the formalisation has adopted.

### 1.2 Lemma 20 — the induction invariant is not preserved

*Blueprint:* `note-lem20`. *Lean:* `SocialNetwork.isConsensus_state_of_favouring`.

The invariant of the written proof, `Ũₖ (a, p) ≤ n(u) + r - (k+1)/(M-1)` for
`p ≠ o`, is not preserved: the actor that expresses at step `k` has its row reset
to `0`, and at the terminal `k` the bound is negative.

**What is needed:** a preserved invariant.  The blueprint proposes
`max (0, n(u) + r - (k+1)/(M-1))` together with a staircase mechanism that
replenishes the witnesses, again as a proposal to check.

### 1.3 Proposition 22 — withdrawn

*Blueprint:* `note-prop22`, `prop22`. *Lean:* `SocialNetwork.Bias.entry_mem_of_nearGreedy`,
**proved**.

An earlier version of this file told you that Proposition 22 does not follow from
Proposition 6: in the repeat case the near-greedy event leaves a slack at the
repeat time, and the chain ended at `N - 1 + 1/(2γ)`, not below `N` for
`γ < 1/(M-1)`.  **That was this repository's error, not yours.**  Your
Appendix C writes the slack as `½γ` — in Remark 7, in
`ζ_{α,β} = e^{βγ/2}/(e^{βγ/2} + MN)`, and in the exponents `e^{-βγ/2}` of
Lemmas 28 and 29 and Corollary 30 — and the repository had transcribed it as
`1/(2γ)` throughout.  With `½γ` the chain ends at `N - 1 + ½γ < N`, and
Proposition 22 follows from Proposition 6 exactly as you say.  It is proved,
and Theorem 25 with it, by the route you prescribe.

Two details of the proof, neither a decision.  The lower bound `-MN` comes from
the row sums, which equation (6) makes `(M-1) α nₐ ≥ 0` rather than `0`, so it
uses `α > 0`; and, as in Proposition 6, the passage from the bound at the repeat
time to the bound at step `N` is carried out explicitly.

The suggestions this section used to make — a proof using the feedback
`u(a,p) ≤ nₐ`, a weaker constant, or weakening Proposition 17 — are withdrawn
with it.

### 1.4 Proposition 7 — the written route needs a step that is not there

*Blueprint:* `prop7`. *Lean:* `SocialNetwork.isLadder_state_of_greedy`,
**proved** (modulo Lemmas 19 and 20).

The written proof has three stages and its arithmetic is right.  What it does not
have is the glue between the first two.

Lemma 19 delivers `Ũ_{τ(u)} ∈ ⋃_o S^o` at the first repeat `τ(u)`.  The proof of
Proposition 7 then writes

> so by Lemma 19 we have `⋂_{j=1}^{N+1} ξ_j^u ⊆ {Ũ_{N+1} ∈ ⋃_o S^o}`

— that is, it carries the membership from `τ(u)` up to `N+1`, using only
`τ(u) ≤ N+1`.  That carry needs **`⋃_o S^o` to be stable under a greedy
expression**, which is neither stated nor proved anywhere.

It is not a formality.  A greedy expression in `S^o` does express `o`
(Lemma 21 of the formalisation's numbering — `opinion_eq_of_isMax_of_favouring`),
but it resets the row of the expressing actor, and that actor may be one of the
witnesses `a₁(u), …, a_{n(u)}(u)`.  New witnesses have to be produced from the
actors that just gained a unit on column `o`, and the bound
`u(a,p) ≤ n(u) + r - 1/(M-1)` on the other columns then has to be re-established
with the *new* `n` and `r`.  That is exactly the bookkeeping of Lemma 20, whose
written invariant does not survive either (§1.2).

**What was done, and why it is not a repair you have to check.**  Lemma 20 is
applied where Lemma 19 actually lands — at `τ(u)` — instead of at `N+1`.  Then no
stability of `S^o` is needed at all, and the arithmetic is yours, unchanged:

```
τ(u) + (M-1)(n(u)+1) - 1  ≤  (N+1) + (M-1)N - 1  =  MN.
```

The written proof needs a *second* carry of the same kind, from
`N+1 + (M-1)(n(u)+1) - 1` up to `MN`, and that one is unavoidable — the last stage
must start at `MN` for the total to be `(M+1)N`.  It is also available: it is your
own observation from the last stage of this same proof, that a greedy expression
in `C^o` expresses `o` and that `C^o` is stable under it.  So the formalisation
keeps that carry and drops the other.

**Nothing here needs a decision.**  It is recorded because the paper as printed
asserts a step that does not follow, and you may want either to add the `S^o`
stability lemma or to restate Proposition 7's proof along the shorter route.

### 1.5 Lemma 28 — inherits Lemma 13's missing displays

*Blueprint:* `lem28`. *Lean:* `SocialNetwork.Bias.biasedProbHitting_le`.

Lemma 28 is Lemma 13 with `1/((M+1)N)` replaced by `½γ`, and Appendix C gives
it no proof of its own.  Lemma 13's proof runs on two inequalities the paper
displays inside proofs and never states (§2.7); the biased proof needs those two
in biased form, and they are not in the paper either.

So Lemma 28 is unproved not because its own argument fails but because the
argument it is told to copy rests on statements that do not exist.  Once §2.7 is
settled the same two transcriptions serve here.  Of its remaining ingredients,
Proposition 22 is proved (§1.3) and Proposition 23 waits on biased analogues of
Lemmas 19 and 20.

The Lean statement was also wrong, and that was a fault of this repository rather
than of the paper; it is now restated in the paper's own form.  See §2.9.

### 1.6 Proposition 9 — "without visiting `u`" does not come from Proposition 7

*Blueprint:* `aux-greedy-avoids`. *Lean:* `SocialNetwork.skeleton_ne_of_greedy`.
*Proposition 9 itself:* `SocialNetwork.measure_le_of_notMem_steepLadderSet`,
**proved** modulo this one step (and, through Proposition 7, modulo Lemmas 19
and 20).

The proof of Proposition 9 bounds the return time below by

> we first consider Proposition 7 to show that a sequence of events `ξ_j^u`,
> `j = 1, …, (M+1)N`, leads the process to `L`, **without visiting `u`**, with a
> lower bounded probability.

Proposition 7 says where the greedy run *ends* — at a ladder, after `(M+1)N`
expressions — and says nothing about where it passes.  The clause is needed:
Kac's inequality bounds `μ̃^β(u)` by the probability of avoiding `u` at *every*
one of the first `m` times, so a single return inside the transient makes the
event empty and the bound vacuous.

After the run has reached `L̂` the claim is immediate, and that part is
formalised: the process stays in `L̂` (Remark 5) and `u ∉ L̂`.  What is missing is
only the times `1 ≤ k < (M+1)N`.

**It is not a formality.**  Greedy runs do return to matrices they have already
visited: from a ladder they cycle with period `N`, three of them for `N = 3`,
`M = 2`.  So the hypothesis `u ∉ L̂` is doing work, and an argument that rules out
a return has to use it.  A monotone quantity will not do it either — the maximum
entry can fall along a greedy step, and on the ladder cycle every symmetric
function of the matrix is constant.

**This no longer needs anything from you.**  It is Corollary 8 of [GL24], stated
there for `M = 2` and proved "directly by Part 2 of Proposition 5, by
contradiction".  Written out: suppose the run returns to `u` at step `k`, and
repeat its first `k` expressions for ever.  The greedy event at a step reads only
the matrix and the expression at that step, and the repeated realisation has the
same state at `n` as the original at `n mod k` — which is where the return is
used — so it is greedy at *every* step and sits at `u` at every multiple of `k`.
Proposition 7 puts it on `L` at step `(M+1)N`; a greedy expression on a steep
ladder is made from a positive entry, so Remark 5 keeps it on `L̂` from there on,
including at the multiple `k(M+1)N`.  Hence `u ∈ L̂`, against the hypothesis —
and the hypothesis is used exactly once, at that last step.

The argument is deterministic, so it needed no restart and no Markov property,
and it is stated on one realisation.  **Proved**; Proposition 9 now rests only on
Lemmas 19 and 20, through Proposition 7.  [`GL24.md`](GL24.md) §2.1 records how
it was found.

### 1.7 Lemma 14 — the conditioning of Appendix B

*Blueprint:* `lem14`, `note-lem14`. *Lean:* `SocialNetwork.le_probHittingGT_consensusOther`,
`SocialNetwork.probHittingLE_consensusOther_le`, **proved**; and
`SocialNetwork.Bias.le_biasedProbHittingGT`, `SocialNetwork.Bias.biasedProbHittingLE_le`
for Lemma 29, **proved**.

The mechanism of Appendix B is right, and so are its estimates: from `L^o` the
process stays in `L̂^o` until an opinion `p ≠ o` is expressed; against a negative
pressure that is a failure, at rate at most `NM e^{-β/(M-1)}`; by the null row it
opens a block in `Ĉ^o`, at rate at most `NM`, and the block returns to `L^o`
unless it is not greedy, which has probability at most `1 - ζ_β^{len}` by
Proposition 8 and Remark 4.

What does not hold together is the composition.  The proof bounds
`P(τ₁⁻ᵒ ≥ t)` and `P(τ₂⁻ᵒ ≥ t | τ₁⁻ᵒ ≥ t)` and multiplies.  The second is reached
through

> `P(T_{n_j} - T_{n_{j-1}} > t | τ₁⁻ᵒ ≥ T_{n_j}) ≥ P(E_j ≥ t)`

and a geometric number `G` of the `E_j`, taken independent of them.  Neither step
is argued, and the first conditions on an event that involves the interval it
bounds: asking that no negative expression occur before `T_{n_j}` favours short
intervals, which is the wrong direction for a lower bound.  The rate bounds the
text appeals to give domination conditionally on the past, not conditionally on
that event.

**What was done.**  The same rates are composed by a first-step comparison with an
exponential clock, by induction on the number of jumps.  A state is in phase `0`
if it lies in `L̂^o`, and in phase `j ≥ 1` if it lies in `Ĉ^o ∪ C^o` and `j`
greedy expressions take it to `L̂^o`; from phase `j`, `C^{-o}` is avoided before
`min(t, T_n)` with probability at least `ζ_β^j e^{-Λt}`, with your
`Λ = 2N³(M+1)³e^{-β/(M-1)}`.  The two failure modes are handled at once, so no
conditioning between them is needed, and the constant is yours.

Two smaller differences, neither costing anything.  A block is the `N`
expressions of the last stage of Proposition 7 rather than all `(M+1)N` — that
stage is all a block uses, and it does not rest on Lemmas 19 and 20 — which only
shortens the constant; Remark 6 makes the same choice.  And Theorem 1.1 is not
used: "not reached before `min(t, T_n)`" decreases to "not reached before `t`"
whether or not the jump times accumulate.

**Lemma 29 follows as Lemma 14**, as Appendix C says, with Proposition 24 in place
of Proposition 8.  Two steps the slack `½γ` changes are supplied: in `C_α^o` a
positive pressure for `o` is at least `(1+γ)/2` — the row is ahead of each other
opinion by a positive multiple of `1 + γ`, and the row sums of (6) are
`(M-1) α nₐ ≥ 0` — so a near-greedy expression expresses `o`; and since `½γ < 1`,
a near-greedy run in a block comes from `N` distinct actors and lands on `L_α^o`.
`Ĉ_α^o` is your `Ĉ^o` with the bound on the other opinions lowered from `1` to
`1 - ½γ`.

**Nothing here needs a decision.**  It is recorded because the written proof
asserts a conditioning that does not follow, and you may want to restate it
along the induction.

---

## 2. Statements that had to be changed

These are not gaps in reasoning; they are places where the statement as written
cannot be used, and the Lean statement differs from the paper's display.

| # | Where | What is wrong | What was done |
|---|---|---|---|
| 2.1 | **Proposition 12**, (15)–(18) | `ε₁ ε₂ s₁ s₂` are introduced before `β`, but Section 5.3 instantiates them at `s₂ = 2β` and `ε₂ = (M+1)²N²e^{-β/((M+1)N)}`, and needs `ε₁ + ε₂ ≤ 1/2` only "for β sufficiently big".  Bound as constants ahead of `β`, **the hypotheses are unsatisfiable** — Theorem 3 could never have been derived from them. | Made functions of `β`; (15)–(18) required only above a threshold `β₁`.  Theorem 3 now follows. |
| 2.2 | **Corollary 15** (and 30) | Quantifies over `l ∈ L^o` and concludes about `L^o`, so it is vacuous unless `L^o ≠ ∅`, which the paper never records. | `SocialNetwork.ladderOf` and `SocialNetwork.Bias.biasedLadderOf` supply the witnesses — the staircase itself, and the profile in which actor `a` has heard exactly `a` expressions of `o`.  Blueprint `aux-ladder-nonempty` and `aux-biased-ladder-nonempty`.  Both corollaries are now proved. |
| 2.3 | **Equation (6)** | The second condition is not stable under `π_α^{a,o}`, though the justification the paper gives for it proves a stronger condition that is. | Blueprint `note-eq6`; the stronger condition is what `IsBiasedState` carries. |
| 2.4 | **Definition 4** | Needs a sign condition to be the set the proofs use. | Blueprint `note-def4`; recorded, and the Lean definition carries it. |
| 2.5 | **Equation (13)**, the transfer | The statement takes *both* `μ` and `μ̃` as given and concludes the formula.  Combined with uniqueness for the skeleton it yields the **uniqueness** half of Theorem 1.2 — but not existence, since it presupposes that `μ` exists. | Not changed, and **proved** as stated, together with the uniqueness half it yields (`eq_of_invariantCts`).  The converse direction — "the measure defined by (13) from `μ̃` is invariant for the semigroup" — is what existence needs and what the paper uses, and is not what is stated; it is **proved** too (`ctsOfSkeleton_spec`), so Theorem 1.2 is.  Whether to restate (13) is your call, and nothing waits on it. |
| 2.6 | **Theorem 31** | Its route needs a biased analogue of Proposition 12, which the paper does not state: Proposition 12 is over `Pressure N M` and Theorem 31 lives over `Profile N M`.  Proposition 23 likewise has no biased analogues of Lemmas 19 and 20 to assemble from. | The analogue is now declared as a second axiom and **Theorem 31 is written out** from it; it rests on Lemma 28 besides.  See §3.3.  Proposition 23 is untouched. |
| 2.7 | **Lemma 13** | Its proof rests on two inequalities the paper displays but never states: the bound on `P (R^{β,u} (L) > t)` inside the proof of part 2 of Theorem 2, and equation (19), which reads Corollary 11 quantitatively.  Theorem 2.2 and Corollary 11 are *both* stated only as limits, and a limit has thrown the rate away, so **Lemma 13 does not follow from the numbered statements it cites**. | The two displays are transcribed verbatim as Lean statements of their own — `probHittingGT_ladderSet_le_of_ne_zero` and `probHittingGT_ladderSet_zero_le`, blueprint `aux-hitting-rate` and `eq19` — each carrying a `sorry`, and Lemma 13 is proved from them.  They were filed here as *citations from outside the paper*, which was wrong: they are steps of your own proofs of part 2 of Theorem 2 and of Corollary 11, and [GL24] writes both out at its p. 19 — the first as its equations (16)–(18), the second as its Corollary 13.  Both are now **proved**: the first along the [GL24] argument, modulo Lemmas 19 and 20; the second outright, from a restart of the continuous-time process at its first jump (§4).  **Your call** whether either should become a numbered statement of the paper. |
| 2.8 | **Proof of Lemma 13**, the term `P (τ > β)` | `τ` is declared exponential of mean `1/(MN)`, for which `P (τ > β) = e^{-MNβ}`; the proof writes `e^{-β/(MN)}`. | Harmless, and no decision needed: `e^{-MNβ} ≤ e^{-β/(MN)}` for `β ≥ 0`, so the written form is the weaker of the two and Lemma 13 follows from either.  The Lean statement uses the written form, so it assumes the weaker one. |
| 2.9 | **Lemma 28**, as formalised | The Lean statement was about the skeleton path measure and the discrete steps `k ≤ ⌈2β⌉`, not the continuous-time hitting time `R^{α,β,u}`, and it bound `C` *after* `β` and `u`, so the constant could depend on both.  It therefore could not serve as (16) for the biased Proposition 12, which is what the lemma exists for. | Restated in the shape of Lemma 13 with `1/((M+1)N)` replaced by `½γ`, and `C` quantified in front.  **A formalisation-side correction, not a correction to the paper** — the paper's display was right all along. |
| 2.10 | **Proposition 9** | The statement quantifies over `β > 0` and `u ∉ L̂`, with no hypothesis on `u` beyond that; its proof calls Proposition 7, which is stated for `u ∈ S`, and the whole paper works in `S`. | `IsState u` added to the Lean statement.  Also stated for an *arbitrary* invariant probability measure of the skeleton rather than for a named `μ̃^β`, since its existence is Theorem 1.2 — which, with Kac's inequality in place of Kac's identity, Proposition 9 no longer needs. |
| 2.11 | **Corollary 11**, as formalised | The Lean statement rendered "`τ` exponential of mean `1/(MN)`, independent from `(U_t^{β,u})_t`" as a supremum over `s ≥ 0` of `e^{-MNs} · P(R^{β,0}(L) > s + ε_β)`.  Its `s = 0` term is `P(R^{β,0}(L) > ε_β)` at weight `1`, which tends to **one**, so the statement was **false**. | Restated as `P(R^{β,0}(L) > T₁ + ε_β) → 0` with `T₁` the process's own first jump time — `probHittingGTAfterFirstJump` — which from `0` is exponential of mean `1/(MN)` (`totalRate_zero`, now proved).  **A formalisation-side correction, not a correction to the paper.**  But see the reading below: your `τ` has to be `T₁`, and the sentence can be read otherwise. |
| 2.12 | **Proof of Theorem 2.1**, the bound on `μ̃^β (L)` | The proof writes `μ̃^β (L) ≥ ζ_β^{(M+1)N} = (e^{β/(M-1)} / (e^{β/(M-1)} + MN))^{(M+1)N} ≥ (MN)^{-(M+1)N}`.  The last inequality fails for small `β`: at `β = 0`, `ζ_0 = 1/(1+MN) < 1/(MN)`. | Harmless, and no decision needed: `ζ_β ≥ 1/(1+MN)` for every `β ≥ 0`, and any constant independent of `β` serves, so the Lean proof uses `(1+MN)^{-(M+1)N}` and only the value of `C` changes.  At `β = 0` itself, where Proposition 9 and Corollary 10 are stated only for `β > 0`, the theorem holds because `C ≥ 1`. |

---

## 3. The two axioms

### 3.1 Proposition 12 is a citation, not a theorem of this paper

`SocialNetwork.exitTime_approx_exponential` is declared as an `axiom`.  The paper
derives Proposition 12 from Theorem 5.3 of [LM22], a metastability estimate for a
general time-homogeneous strong Markov process.  Nothing inside this repository
can discharge it, so leaving it as a `sorry` would have made it look like work
someone could pick up.  CI now fails if any result claimed complete reaches it,
and a separate step records what is true only modulo it.

### 3.2 It cannot be stated once for both models

An earlier note in this project suggested stating Proposition 12 abstractly, over
an arbitrary family of measures and an arbitrary hitting time, so that Theorems 3
and 31 could share it.  **That suggestion was wrong: such an axiom is
inconsistent.**  Take the zero measure with an empty ladder set — (15)–(18) hold
vacuously and the conclusion fails at `t = 0`.  What excludes that is the strong
Markov property, which is the entire content of [LM22] and is not expressible
here.

So the axiom is attached to the concrete process, as the paper states it, and
Theorem 31 needs its own twin.

### 3.3 The twin, added on your instruction

`SocialNetwork.Bias.biasedExitTime_approx_exponential` is the same statement over
`Profile N M` instead of `Pressure N M`.  Appendix C never states it: it says only
that "the proof of Theorem 31 follows exactly as the proof of Theorem 3", and that
proof runs through Proposition 12, which is stated for the unbiased process alone.

**So the repository now asks you to trust two things, not one**, and they are the
same citation applied twice.  If [LM22] Theorem 5.3 is right, both are right; the
duplication is a limitation of what can be *stated* here, not a second
mathematical assumption.  Should you prefer a single hypothesis, the way to get it
is to formalise enough of the strong Markov property that the abstract version
stops being vacuous — that is real work, and it is the only honest route.

CI gates both: no result claimed complete may reach either, and the inventory step
now records what is true modulo each of them separately.

---

## 4. Steps asserted in the text, argued here

None of these is new mathematics and none needed a decision; they are recorded so
that you know where the written argument leaves a step to the reader.  The
blueprint's audit section classifies every formalised proof this way.

* **Remark 5.**  The paper writes the two inequalities defining `η` in one line
  and argues neither.  The comparison showing the worst case over `L̂` is attained
  on `L` rests on a monotone form of a gap in Mathlib.
* **Remark 5 iterated.**  The `m`-step bound `η^m` is used in the sketch of
  Proposition 9 without being derived.
* **Proposition 9, the composition.**  The greedy run of Proposition 7 and the
  positive expressions of Remark 5 are composed on the realisation — the two are
  one event of the sample space — rather than by restarting the chain at time
  `(M+1)N`, which is how the paper reads it.
* **Proposition 9, the constant.**  Reaching the printed `C' = (NM)^{(M+1)N+1}`
  needs the regime `MN e^{-β/(M-1)} > 1` treated separately: there `C'` already
  exceeds `e^{β(N-1)}` and `μ̃^β(u) ≤ 1` suffices.  The paper does not split.
* **Remark 8.**  The case `k ≥ 1` is supplied; the count `cₚ` the pigeonhole
  returns is kept rather than rounded to `⌈nₐ/M⌉`, which only enlarges the
  intermediate bound.
* **Proposition 6.**  The passage from the repeat time to the global bound, which
  the paper compresses into "this implies", is carried out explicitly.
* **Proposition 7.**  The "by definition" at the end; blueprint `note-prop7`.
* **Proposition 8.**  The iteration over `m`, which the paper does by conditioning
  in (10), goes through the Ionescu–Tulcea kernels — Mathlib offers no
  decomposition of that shape.  Same Markov property, different formalism.
* **Corollary 11 and equation (19), the restart.**  Both read the process after
  its first expression — "conditionally on the first jump" — and the paper does
  not say in what sense.  In Lean it is the Markov property at the first jump for
  the jump–hold representation, proved from the construction: one step of the
  driving kernel keeps the history and appends a step drawn at the matrix that
  history reaches, so dropping the first entry of a history shifts that reading by
  one.  The corresponding statement about hitting times,
  `R^{β,u}(θ)(ω) ≤ T₁(ω) + R^{β,v}(θ)(σω)`, needs every holding time positive,
  which is almost sure, and splits on the jump counter: on the explosion event the
  counter is junk on both sides, and there the matrix at stake is the one the first
  expression reaches, shown at `T₁` itself.  Theorem 1.1, now proved, makes that
  event null and would remove the case; the proof still handles it directly, and
  is unchanged.
* **Proposition 21.**  The quantity that resets and grows by one per step is `nₐ`,
  not the row supremum; the passage is `u (a, p) = cₚ(1+γ) - γnₐ ≤ nₐ`.
* **Propositions 17 and 24.**  Appendix C invokes the proofs of Propositions 6
  and 8 in one sentence each, and for these two that is right.  The iteration
  common to both is run once in Lean, for an arbitrary choice of admissible
  pairs at each profile, since neither uses anything else about its event.
* **Theorem 3 / Section 5.3.**  Three steps: the inclusion `L ⊆ L^o ∪ C^{-o}`
  (the paper cites a bound about `L` for a condition about `L^o ∪ C^{-o}`); the
  supremum `sup_{β≥0} β e^{-β/a} = a e^{-1}` of step (20); and an explicit
  threshold above which `ε₁ + ε₂ ≤ 1/2`.  Proposition 12 also fixes an opinion
  while Theorem 3 quantifies over it, so the constants are taken uniform over the
  finitely many opinions.
* **Theorem 2.1.**  Four steps of pp. 20–21 are asserted and supplied: the bound `q_β(l) ≤ MN e^{β(N-1)}` on `L`; the invariance under the `(M+1)N`-step kernel that turns Propositions 7 and 8 into `μ̃^β(L) ≥ ζ_β^{(M+1)N}`; that a state off `L` whose entries are all below `N` is off `L̂` — `N` distinct integers in `{0, …, N-1}` are all of them, which needs the sign condition of §2.4; and that there are finitely many such states, `K(N, M) < ∞`, which follows from the row sums of Remark 3.  The last step, `1/(1+x) ≥ 1 - x`, is taken on the complement, as `μ^β(Lᶜ) = B/(A+B) ≤ B/A`.
* **Lemma 13.**  "Putting the inequalities above together" is the comparison of
  each of the three terms with `e^{-β/((M+1)N)}` — using `MN ≤ (M+1)N`,
  `M - 1 ≤ (M+1)N` and `e^{β/(M-1)} ≥ 1` — which leaves the integer inequality
  `1 + (M+1)N ≤ (M+1)N²`, true since `N ≥ 3`.  It is tight enough to be worth
  writing down: the greedy term alone already uses `M(M+1)N²` of the `(M+1)²N²`
  available.
* **Lemma 14.**  That the expression of `p ≠ o` by the null row "leads the
  process to `Ĉ^o`": the others lose `1/(M-1)` towards `o`, which keeps them
  non-negative, and gain `1` towards `p`, which keeps them below `1`; with
  `N ≥ 3` one of them still carries at least `1` for `o`.
* **Lemma 29.**  The two steps the slack changes, at §1.7.
* **Proposition 22.**  As at Proposition 6, the passage from the repeat time to
  the bound at step `N` is carried out explicitly.
* **Corollary 30.**  Appendix C gives it as "the rearrangement of Corollary 15
  with `1/(M-1)` replaced by `½γ`", and it is exactly that; the Lean proof is
  Corollary 15's, transposed.
* **Theorem 31.**  Appendix C says only "the proof follows exactly as the proof of
  Theorem 3", and names none of the constants.  The four taken here are what
  Section 5.3 produces with `½γ` in place of `1/(M-1)`: `s₁ = 1`,
  `ε₁ = 2N³(M+1)³e^{-βγ/2}`, `s₂ = 2β`, `ε₂ = Ce^{-βγ/2}` with `C` from
  Lemma 28, and `δ = θ = γ/4` — the exponent halved to absorb the factor `β` of
  step (20), which is why the two coincide here where the unbiased proof had
  `1/((M+1)N)` and `1/(2(M-1))`.  The threshold above which `ε₁ + ε₂ ≤ 1/2` is
  `β₁ = max(1, (4/γ)(2N³(M+1)³ + C))`.
* **Equation (13), the correspondence.**  "A probability measure is invariant for
  the process if and only if its product with the jump rate is invariant for the
  skeleton chain" is cited and not proved.  Both directions are proved here: the
  one (13) consumes from a lower bound on `P_t`, the converse — which existence in
  Theorem 1.2 needs — from the decomposition of `P_t` along the number of jumps.
  See the entry below.
* **Equation (13), the rate floor.**  "Since every `u ∈ S` carries an actor with
  null social pressure, the jump rate obeys `q_β(u) ≥ M`" is asserted and not
  argued; and the finiteness of `∑ μ̃^β(u)/q_β(u)`, without which the
  right-hand side of (13) is not a probability measure, is not stated at all.
  Both are proved here.
* **Measurability.**  The paper does not address it anywhere.  Every measurability
  lemma here has no counterpart in the text.

---

## 5. Not the paper's fault

Nothing is unproved here any more because Mathlib lacks a theory.

**Lemmas 14 and 29 were the last on this list**, filed as needing a
Kolmogorov-type bound on the convergence to `Exp(1)` and a total-variation
distance.  Appendix B uses neither — it compares exponential clocks — and both
lemmas are proved (§1.7).

`blueprint/blueprint.md` is the engineering audit of what Mathlib does and does
not provide, checked against the pinned revision.

**Theorem 1.1, Theorem 16 and Theorem 1.2 have left this list**: they are proved.
So has the correspondence equation (13) cites, in both directions; see below.

Theorem 1.1 is proved by your sandwich (11) — by [GL24]'s construction of it, pp.
12–14, which is now formalised.  The band of its Figure 2 is built in
`SocialNetwork/Graphical.lean`, its Lemma 10 is read on the marks there, and
`SocialNetwork/Collapse.lean` identifies the realisation the band carries with the
process (3) defines.  Two things are done differently and neither changes a step:
the marks are carried by the jump-hold form rather than by a point process on
`[0,∞)²`, Mathlib having none, and [GL24]'s "`T^λ` is a rate-`λ` Poisson process,
so `sup T^λ_n = ∞`" is proved by a supermartingale instead.  One step is in
neither source — the identification itself, which [GL24] states in passing — and
supplying it is what `SocialNetwork/Collapse.lean` mostly is.

**Theorem 16 follows the same route**, which is what Appendix C prescribes.  The
band is built over an arbitrary state space — a rate per pair per state, the
state each pair leads to, a distinguished family, and a bound `λ` on the rate it
carries — so the biased model instantiates the same theorem with the rates of (7)
and Proposition 21 in place of Proposition 5.  Your biased low family, read off
the pressures of (6), is the only line of the argument the two proofs do not
share.  **Proposition 7 and Lemma 14 are the departures in the development**
(§§1.4 and 1.7), and Lemma 29 inherits the second.

### Equation (13) and Theorem 1.2 are proved, and so is the equivalence they cite

Its proof opens: *"For a non-explosive process, a probability measure is
invariant for `(U_t^{β,u})_t` if and only if its product with the jump rate is
invariant for the skeleton chain. **Non-explosivity holds by Part 1** …"*

**Equation (13) is now proved** — `SocialNetwork.invariantCts_eq_of_invariantSkeleton`,
blueprint node `eq13` — and so is the uniqueness half of Theorem 1.2 that it
yields, `SocialNetwork.eq_of_invariantCts`.

The equivalence you cite is not in Mathlib, so the direction (13) consumes is
proved here, at `SocialNetwork.invariant_rateMeasure` (blueprint
`aux-transfer`): if `μ` is invariant for every `P_t` then `q_β · μ` is a finite
invariant measure of the skeleton.  The route is short and uses none of the
theory the citation suggests.  Only a *lower* bound on `P_t` is needed, and the
jump-hold representation gives it: by time `t` either no jump has occurred or
exactly one has, the two events are disjoint and each is read off the first two
holding times, so

```
P_t (v, w) ≥ [v = w] e^{-q(v)t} + κ(v, w) e^{-q(w)t} (1 - e^{-q(v)t}).
```

Putting that into the invariance equation, dividing by `t` and letting `t → 0`
gives `νκ ≤ ν` for `ν = q_β · μ`; your page-15 minorisation then makes `ν`
finite — `ν(l^o) ≥ c ν(S)` with `ν(l^o) < ∞` — and a finite measure dominating
its own image under a Markov kernel equals it.

Two things worth saying about that route.  **It does not use Theorem 1.1.**
Your appeal to it is discharged, since Part 1 is proved here; but the two events
above are read off the jump counter directly, whether or not the jump times
accumulate afterwards, so non-explosion never enters.  And **it does not use any
Chapman–Kolmogorov identity**: `P_s` is never composed with `P_t`.

The two small steps that were ours are also done: `q_β(u) ≥ M` on `S`, which the
null row of (2) gives, and the finiteness `∑ μ̃^β(u)/q_β(u) ≤ 1/M` that makes the
right-hand side a probability measure at all — `SocialNetwork.IsState.le_totalRate`
and `SocialNetwork.tsum_div_totalRate_le`, blueprint node `aux-rate-floor`.

**The converse is proved too**, and with it existence: `μ̃^β/q_β`, normalised,
*is* invariant for every `P_t` — `SocialNetwork.ctsOfSkeleton_spec`, through
`SocialNetwork.invariantCts_of_bind_rateMeasure_le` (blueprint
`aux-transfer-converse`).  Theorem 1.2 is `SocialNetwork.existsUnique_invariantCts`,
and both directions of the equivalence are `SocialNetwork.isInvariantCts_iff`.

A lower bound on `P_t` cannot give this direction, and it did not need a forward
equation for the semigroup either, which is what we had expected.  It suffices
that `μ P_t ≤ μ` at every matrix, both sides being probability measures.  Write
`P^{(n)}_t (v, w)` for the chance of having made exactly `n` expressions by `t` and
sitting at `w`.  Restarting at the first expression gives `P^{(n+1)} = 𝓑 P^{(n)}`,
where `𝓑` averages over the first step; the induction wants the decomposition
along the *last* expression instead,

```
(𝓛 F)(v, w, t) = ∑_x q(x) κ(x, w) ∫_0^t e^{-q(w) r} F(v, x, t - r) dr,
```

and the two operators commute by Tonelli alone — each averages over an
independent time, and the shifts add in either order — and agree on `P^{(0)}` by
the reflection `r ↦ t - r`.  So `P^{(n+1)} = 𝓛 P^{(n)}`, and an induction on the
number of expressions bounds `∑_v μ(v) ∑_{n<K} P^{(n)}_t(v, w)` by `μ(w)`, since one
more term costs `μ(w) e^{-q(w)t} + q(w) μ(w) ∫_0^t e^{-q(w)r} dr = μ(w)`.

**Here Theorem 1.1 is used, and has to be**: `P_t ≤ ∑_n P^{(n)}_t` misses exactly
the realisations that explode before `t`, and for an explosive chain the measure
need not be invariant at all.  So your "Non-explosivity holds by Part 1" is the
right appeal — for the direction existence needs, not for the one (13) consumes.

The restatement §2.5 asks about is now a matter of presentation only: (13) as
stated gives uniqueness, the converse gives existence, and both are proved.

### Theorem 1.2 for the skeleton, and two remarks on your page 17

`μ̃^β` exists and is unique, proved outright
(`SocialNetwork.existsUnique_invariantSkeleton`), from Doeblin's criterion —
proved here for a general Markov kernel on a countable space, *both halves*,
in `SocialNetwork/Doeblin.lean` — and your page-17 minorisation, in
`SocialNetwork/Minorisation.lean`.

One thing is worth saying because it may affect how you write it: on a
*countable* state space the existence half needs no Markov-chain theory at all.
The excursion measure `ν(y) = ∑ₘ P_l(Ũₘ = y, R_l > m)` is a sum in `[0,∞]`;
your minorisation makes it summable directly, since it gives
`P_l(R_l > m) ≤ (1-c)^m` at once; and invariance is the last-exit
decomposition, which in coordinates is two lines.  No positive recurrence, no
Kac identity, no compactness, no Cesàro limit.

Two remarks on the minorisation, neither of them a request.  Your `ε*` is a
minimum over the finite set of bounded matrices of a probability you do not
compute; the Lean proof has the explicit `e^{-2βR/(M-1)}/MN` per expression
instead, with `R = MN(M-1) + N(M-1)`, since the rates of (3) are exponentials of
bounded exponents — so `ε* ≥ (e^{-2βR/(M-1)}/MN)^N` and the finite set is never
exhibited.  And (12) is proved in the form it is actually used in: the `N`
expressions of `o` in decreasing actor order send **any** matrix to `l^o`, with
no hypothesis on where they start.  That is what lets the minorising measure be
a single Dirac mass, which is what the criterion consumes; it is worth stating
that way if you revise.

### Theorem 25 is proved, by your route

Your Appendix C says the proof "follows exactly as the proof of Theorem 1", and
the proof of Theorem 1 part 2 puts together Propositions 6 and 8; transported,
those are Propositions 22 and 24.  Both are proved here, so Theorem 25 is, along
exactly that route.

An earlier version of this file proposed avoiding Proposition 22 by weakening
Proposition 17, whose proof uses only `γ > 0`.  That is no longer needed.  The
observation about Proposition 17 stands and costs nothing to state if you revise,
but nothing depends on it.

### Proposition 9: the identity needs irreducibility, the inequality does not

The proof opens with the *identity* `1/μ̃^β(u) = E[R̃^{β,u}(u)]`, which does need
the chain to be irreducible — and so, read literally, needs Theorem 1.2.  But
the proof goes on to use only

```
μ̃^β(u) · E[R̃^{β,u}(u)] ≤ 1,
```

since what it wants is an *upper* bound on `μ̃^β(u)`.  **That inequality holds
for every invariant probability measure**, with no irreducibility, no recurrence
and no existence theorem: the events "the last visit to `u` before time `m` was
at time `j`", `j < m`, are disjoint, and stationarity gives each of them
probability `μ̃^β(u) · P_u(R > m-1-j)`.  Only the identity needs the union of
those events to have full measure.  The counterexample to the identity without
irreducibility is two absorbing states with `μ̃ = (½, ½)`, where the return time
is `1` and `1/μ̃` is `2`.

`SocialNetwork/Kac.lean` proves the inequality outright, for a Markov kernel on
a countable space, in about a hundred lines, using nothing from Mathlib beyond
`Kernel.Invariant` and the Lebesgue integral.  Nothing is asked of you; it is
worth a line in a revision that the proof does not need what it opens with.

### Corollary 11: one word of yours decides it

Corollary 11 reads `P(R^{β,0}(L) > τ + e^{-β(1-δ)/(M-1)}) → 0`, "where `τ` is an
exponentially distributed random variable with mean `1/(MN)` independent from
`(U_t^{β,u})_t`".  Everything turns on that superscript `u`.

Read as you use it in equation (19) — `τ` is the process's own first jump time
from `0`, and the independence asserted is from what happens *after* it, from
the state `u` it lands on — the corollary is true and is exactly Theorem 2,
part 2, applied at `u`.  That is the reading the Lean statement carries, and
under it the corollary is proved, as is equation (19).

Read as "`τ` independent of the process", full stop, the corollary is **false**.
From `0` we have `0 ∉ L`, so `R^{β,0}(L) ≥ T₁`, and `R^{β,0}(L) = T₁ + O(ε_β)`;
the left-hand side then tends to `P(T₁ > τ)` with `T₁` and `τ` independent, both
exponential of rate `MN` — which is `1/2`.

**Nothing is asked of you**, and nothing in the paper needs changing: your proof
of Lemma 13 uses the right reading.  It is recorded because the sentence as
written admits a reading under which the corollary fails, and a formalisation is
the kind of reader that takes it.

### Remark 6: the horizon is `N`, not `(M+1)N`

"By following the same steps of the proof of part 2 of Theorem 2" is exactly
right, but the steps have to be run from `C^o` and stopped at `N`: continuing a
greedy run past a ladder expresses the same opinion again and leaves `L^o`, so
part 2's bound — which concludes `L`, not `L^o` — cannot be quoted as it stands.
What Remark 6 uses is the last stage of Proposition 7 on its own, which is why
it is proved outright while part 2 is not: starting inside `C^o` skips Lemmas 19
and 20, since getting to `C^o` is their whole job.

Nothing downstream uses Remark 6 — it strengthens Corollary 11 in the direction
Lemma 14 needs — but it is the only statement of Section 5.2 this repository can
offer you sorry-free.

### Theorem 4 part 1: two supplied steps and one reorganisation

Part 1 is proved, and with it the negative-bias half of the phase transition:
almost surely all but one actor eventually stop expressing.  Proposition 18
supplies the uniform chance of settling, Proposition 17 carries it from `B_N^α`
to the whole of `S^α`, and the failure-time recursion closes it.

Two steps are supplied rather than read off the paper, and both are recorded at
the node in the blueprint.  The first is the Markov property.  You write "the
strong Markov property at time `T_N`", but part 1 is a statement about the
sequence `(A_n)` — about the skeleton — and for the skeleton `T_N` is the
*deterministic* index `N`; so what is used there is the simple Markov property.
At the failure times a real stopping time does appear, and for a discrete-time
chain the strong Markov property follows from the simple one by decomposing over
its countably many values.  Nothing was assumed that you did not use; the proof
names a stronger tool than the argument needs, and Mathlib has no strong Markov
property to hand it.  The second supplied step is that `{η_n < ∞}` is measurable
for the past at `η_n`, which here is the statement that each failure event is
decided by the expressions that precede it.

One reorganisation is worth flagging, since it is visible in the Lean.  Your
recursion gives `P(η_{n+1} < ∞) ≤ (1-c) P(η_n < ∞)` and concludes by letting
`n → ∞`.  That limit is exactly `q = sup_{v ∈ S^α} P_v(no actor is eventually
alone)`, and the single inequality the recursion uses gives `q ≤ (1-c) q` in one
step.  The estimate, the time it is applied at and the constant are yours; only
the bookkeeping of the recursion is replaced by the fixed point it converges to.
Say the word if you would rather see the `η_n` written out.

Two smaller notes.  Theorem 16 is **not** needed for part 1: the statement is
about the sequence of expressed pairs, and non-explosion is what makes the
continuous-time process well defined.  And your part 1 indexes from 1, the
formalisation from 0, so where you write `⋂_{m ≥ N+1} {A_m = A_{N+1}}` the Lean
reads `∀ m ≥ N, A_m = A_N`.

---

## How this file stays honest

Every claim above is checked by the build, not by hand.

[`STATUS.md`](STATUS.md) is generated from `blueprint/src/content.tex` and the
Lean sources by `scripts/status.py`, and CI regenerates it and fails on any
difference.  The same script refuses a `sorry` that no blueprint node accounts
for, a Lean name the blueprint cites but the library does not declare, and an
unproved statement with no recorded reason — so an obstruction cannot be
introduced without appearing here.

The axiom check is generated the same way: it is every declaration cited by a
node the blueprint's dependency graph resolves to *proved*, or to a definition
with nothing to prove, and the build fails if any of them reaches `sorryAx` or
either [LM22] axiom.  A green node in
the blueprint is therefore a claim the build verifies, not a claim someone
remembered to keep true.

If an item here is fixed, the blueprint and this file are updated in the same
commit as the code.
